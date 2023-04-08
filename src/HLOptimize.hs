module HLOptimize where
import Data.Char (ord, chr)
import Data.List (sortBy)
import Data.Maybe(fromMaybe)

import HLDefs
import HLOps
import Typer.TypingDefs

inlineHeuristic :: HLExpr -> Int -> Bool
inlineHeuristic e appears =
    let size = exprSize e
        addedSize = size*(appears - 1)
    in size < 8 || addedSize < size

inlineComb :: Combinator -> HLExpr -> HLExpr
inlineComb cmb e@(_, _, ExprLiteral _) = e
inlineComb cmb e@(_, _, ExprLabel l') = e
inlineComb cmb (c, t, ExprApp f a) = (c, t, ExprApp (inlineComb cmb f) (inlineComb cmb a))
inlineComb cmb (c, t, ExprConstructor cn es) = (c, t, ExprConstructor cn (map (inlineComb cmb) es))
inlineComb cmb@(cn, _, as, e) (c, t, ExprCombinator mcn es)
    | cn == mcn =
        let es' = map (inlineComb cmb) es
            binds = zip (map fst as) es'
            newe = inline binds e
        in newe
    | otherwise = (c, t, ExprCombinator mcn (map (inlineComb cmb) es))
inlineComb cmb e@(c, t, ExprLambda l' le) = (c, t, ExprLambda l' (inlineComb cmb le))
inlineComb cmb (c, t, ExprPut vs pses) = (c, t, ExprPut (map (inlineComb cmb) vs)
    (map (\(p, e)-> (p, inlineComb cmb e)) pses))
inlineComb cmb (_, _, ExprHint _ e) = inlineComb cmb e

inlineDefs :: Combinator -> [Combinator] -> [Combinator]
inlineDefs cmb [] = []
inlineDefs cmb ((ld, il, as, e):defs') = (ld, il, as, inlineComb cmb e):inlineDefs cmb defs'

sortInlines :: MonoProgram -> MonoProgram
sortInlines (ep, defs) =
    let weighted = map (\c@(_,il,_,e)->((il,exprSize e), c)) defs
    in (ep, map snd $ sortBy (\(w,_) (w', _) -> compare w' w) weighted)

--    (ep, sortBy (\(l,il,as,e) (l',il',as',e')->
--        compare (il', (appears l ep + appearsDefs l defs)) (il, (appears l' ep + appearsDefs l' defs))
--    ) defs)

-- TODO: non considera l'esplosione della dimensione a causa di argomenti utilizzati più volte
inlineProgram :: MonoProgram -> MonoProgram
inlineProgram prog = loop [] (sortInlines prog)
    where
        loop procd (ep, []) = (ep, procd)
        loop procd (ep, cmb@(l, il, as, e):defs)
            | (appears l ep + appearsDefs l (procd ++ defs)) == 0
                = loop procd (ep, defs)
            | appears l e == 0 && inlineHeuristic e (appears l ep + appearsDefs l (procd++defs))
                = loop (inlineDefs cmb procd) (inlineComb cmb ep, inlineDefs cmb defs)
            | otherwise = loop (cmb:procd) (ep, defs)

data SieveRes
    = Always [(String, HLExpr)]
    | Maybe
    | Never
concatRess [] = Always []
concatRess (Never:_) = Never
concatRess (Maybe:_) = Maybe
concatRess (Always bs:rs) = case concatRess rs of
    Never -> Never
    Maybe -> Maybe
    Always bs' -> Always (bs ++ bs')


sievePatternInner :: HLPatternData -> HLExpr -> SieveRes
sievePatternInner PatWildcard _ = Always []
sievePatternInner (PatLiteral plit) (_, _, ExprLiteral elit) =
    if plit == elit then Always [] else Never
sievePatternInner (PatVariant pvar ps) (_, _, ExprConstructor evar es) =
    if pvar == evar
    then sievePatternList ps es
    else Never
sievePatternInner p e = Maybe

sievePattern :: HLPattern -> HLExpr -> SieveRes
sievePattern (_, Nothing, patdata) e = sievePatternInner patdata e
sievePattern (_, Just l, patdata) e =
    let inner = sievePatternInner patdata e
        in concatRess [Always[(l, e)],inner]

sievePatternList :: [HLPattern] -> [HLExpr] -> SieveRes
sievePatternList ps es = concatRess (zipWith sievePattern ps es)

sievePatterns :: [HLExpr] -> [([HLPattern], HLExpr)] -> [([HLPattern], HLExpr)]
sievePatterns v = reverse . loop []
    where loop pses' [] = pses'
          loop pses' ((p, e):pses) =
            case sievePatternList p v of
                Always _ -> (p, e):pses'
                Maybe -> loop ((p, e):pses') pses
                Never -> loop pses' pses

optimizeBI c t "spinnaker_addInt" [(_, _, ExprLiteral (LitInteger i0)),(_, _, ExprLiteral (LitInteger i1))] = (c, t, ExprLiteral (LitInteger (i0+i1)))
optimizeBI c t "spinnaker_subInt" [(_, _, ExprLiteral (LitInteger i0)),(_, _, ExprLiteral (LitInteger i1))] = (c, t, ExprLiteral (LitInteger (i0-i1)))
optimizeBI c t "spinnaker_mulInt" [(_, _, ExprLiteral (LitInteger i0)),(_, _, ExprLiteral (LitInteger i1))] = (c, t, ExprLiteral (LitInteger (i0*i1)))
optimizeBI c t "spinnaker_divInt" [(_, _, ExprLiteral (LitInteger i0)),(_, _, ExprLiteral (LitInteger i1))] = (c, t, ExprLiteral (LitInteger (quot i0 i1)))
optimizeBI c t "spinnaker_remInt" [(_, _, ExprLiteral (LitInteger i0)),(_, _, ExprLiteral (LitInteger i1))] = (c, t, ExprLiteral (LitInteger (rem i0 i1)))
optimizeBI c t "spinnaker_equInt" [(_, _, ExprLiteral (LitInteger i0)),(_, _, ExprLiteral (LitInteger i1))] = (c, t, ExprConstructor (if i0 == i1 then "True" else "False") [])
optimizeBI c t "spinnaker_neqInt" [(_, _, ExprLiteral (LitInteger i0)),(_, _, ExprLiteral (LitInteger i1))] = (c, t, ExprConstructor (if i0 /= i1 then "True" else "False") [])
optimizeBI c t "spinnaker_leqInt" [(_, _, ExprLiteral (LitInteger i0)),(_, _, ExprLiteral (LitInteger i1))] = (c, t, ExprConstructor (if i0 <= i1 then "True" else "False") [])
optimizeBI c t "spinnaker_greInt" [(_, _, ExprLiteral (LitInteger i0)),(_, _, ExprLiteral (LitInteger i1))] = (c, t, ExprConstructor (if i0 > i1 then "True" else "False") [])

optimizeBI c t "spinnaker_addFlt" [(_, _, ExprLiteral (LitFloating f0)),(_, _, ExprLiteral (LitFloating f1))] = (c, t, ExprLiteral (LitFloating (f0+f1)))
optimizeBI c t "spinnaker_subFlt" [(_, _, ExprLiteral (LitFloating f0)),(_, _, ExprLiteral (LitFloating f1))] = (c, t, ExprLiteral (LitFloating (f0-f1)))
optimizeBI c t "spinnaker_mulFlt" [(_, _, ExprLiteral (LitFloating f0)),(_, _, ExprLiteral (LitFloating f1))] = (c, t, ExprLiteral (LitFloating (f0*f1)))
optimizeBI c t "spinnaker_divFlt" [(_, _, ExprLiteral (LitFloating f0)),(_, _, ExprLiteral (LitFloating f1))] = (c, t, ExprLiteral (LitFloating (f0/f1)))
optimizeBI c t "spinnaker_equFlt" [(_, _, ExprLiteral (LitFloating f0)),(_, _, ExprLiteral (LitFloating f1))] = (c, t, ExprConstructor (if f0 == f1 then "True" else "False") [] )
optimizeBI c t "spinnaker_neqFlt" [(_, _, ExprLiteral (LitFloating f0)),(_, _, ExprLiteral (LitFloating f1))] = (c, t, ExprConstructor (if f0 /= f1 then "True" else "False") [] )
optimizeBI c t "spinnaker_leqFlt" [(_, _, ExprLiteral (LitFloating f0)),(_, _, ExprLiteral (LitFloating f1))] = (c, t, ExprConstructor (if f0 <= f1 then "True" else "False") [] )
optimizeBI c t "spinnaker_greFlt" [(_, _, ExprLiteral (LitFloating f0)),(_, _, ExprLiteral (LitFloating f1))] = (c, t, ExprConstructor (if f0 > f1 then "True" else "False") [] )
optimizeBI c t "spinnaker_convItoF" [(_, _, ExprLiteral (LitInteger i))] = (c, t, ExprLiteral (LitFloating (fromIntegral i)))
optimizeBI c t "spinnaker_floorFlt" [(_, _, ExprLiteral (LitFloating f))] = (c, t, ExprLiteral (LitInteger (floor f)))

optimizeBI c t "spinnaker_convItoC" [(_, _, ExprLiteral (LitInteger i))] = (c, t, ExprLiteral (LitCharacter (chr i)))
optimizeBI c t "spinnaker_convCtoI" [(_, _, ExprLiteral (LitCharacter ch))] = (c, t, ExprLiteral (LitInteger (ord ch)))

optimizeBI c t "spinnaker_andBool" [(_, _, ExprConstructor b0 []),(_, _, ExprConstructor b1 [])] =
    let b = case (b0, b1) of
            ("True", "True") -> "True"
            ("True", "False") -> "False"
            ("False", "True") -> "False"
            ("False", "False") -> "False"
    in (c, t, ExprConstructor b [])
optimizeBI c t "spinnaker_orBool" [(_, _, ExprConstructor b0 []),(_, _, ExprConstructor b1 [])] =
    let b = case (b0, b1) of
            ("True", "True") -> "True"
            ("True", "False") -> "True"
            ("False", "True") -> "True"
            ("False", "False") -> "False"
    in (c, t, ExprConstructor b [])
optimizeBI c t "spinnaker_notBool" [(_, _, ExprConstructor b0 [])] =
    let b = case b0 of
            "True" -> "False"
            "False" -> "True"
    in (c, t, ExprConstructor b [])

optimizeBI c t l es = (c, t, ExprCombinator l es)

optimizeExpr :: HLExpr -> HLExpr
optimizeExpr e@(_, _, ExprLiteral _) = e
optimizeExpr (c, t, ExprApp f a) =
    let f' = optimizeExpr f
        a' = optimizeExpr a
    in case f' of
        (_, _, ExprLambda l inner) -> optimizeExpr (c, t, ExprPut [a'] [([(c, Just l, PatWildcard)], inner)])
        _ -> (c, t, ExprApp f' a')
optimizeExpr e@(_, _, ExprLabel _) = e
optimizeExpr (c, t, ExprConstructor l es) = (c, t, ExprConstructor l (map optimizeExpr es))
optimizeExpr (c, t, ExprCombinator l es) = optimizeBI c t l (map optimizeExpr es)
optimizeExpr (c, t, ExprPut vals pses) = --TODO: putofput
    let vals' = map optimizeExpr vals
        pses' = sievePatterns vals' pses
        pses'' = map (\(p,e)->(p,optimizeExpr e)) pses'
    in case pses'' of
        [(p, e)] -> case sievePatternList p vals' of
            Always bs -> 
                if all (\(ml,me)->inlineHeuristic me (appears ml e)) bs
                then optimizeExpr $
                    --TODO: questo effettua un inline forse troppo permissivo
                    foldl (\me (l,e')->inline [(l, e')] me) e bs
                else (c, t, ExprPut vals' pses'')
            _ -> (c, t, ExprPut vals' pses'')
        _ -> (c, t, ExprPut vals' pses'')
        --error $ "OPTIMIZED val " ++ show val' ++ "\npses " ++ show pses ++ "\npses'" ++ show pses'
optimizeExpr (c, t, ExprLambda pat e) = (c, t, ExprLambda pat (optimizeExpr e))
optimizeExpr (_, _, ExprHint _ e) = optimizeExpr e

liftComb :: Combinator -> (Combinator, Combinator) --lambda e lifted
liftComb (l, il, as, e) =
    let (clts, e'@(innerc, innert, _)) = liftLambda e
        newlab = l ++ "lifted"
        newas = map (\(myl, myat) -> (myl ++ "lifted", myat)) as
        newclts = map (\(myc, (myl, myat)) -> (myc, (myl ++ "lifted", myat))) clts
        newinner = (innerc, innert, ExprCombinator newlab (map (\(al, at) -> (innerc, at, ExprLabel al)) $ newas ++ map snd newclts))
        newlam = foldr (\(myc, (myl, myat)) mye@(_, myrt, _) -> (myc, buildFunType myat myrt, ExprLambda myl mye)) newinner newclts
    in ((l, True, newas, newlam), (newlab, il, as ++ map snd clts, e'))
    where --liftLambda :: HLExpr -> ([(StdCoord, (String, DataType))], HLExpr)
          liftLambda (c, DataTypeApp (DataTypeApp _ a) _, ExprLambda l le) =
            let (clts, le') = liftLambda le in ((c, (l, a)):clts, le')
          liftLambda (_, _, ExprHint _ e) = liftLambda e
          liftLambda e = ([], e)
liftCombs :: MonoProgram -> MonoProgram
liftCombs (ep, defs) =
    let (lams, lifts) = unzip $ map liftComb defs
    in (foldr inlineComb ep lams, foldr inlineDefs lifts lams)

optimizeDefExprs :: MonoProgram -> MonoProgram
optimizeDefExprs (ep, defs) = (optimizeExpr ep,
            map (\(l,il,as,e)->(l,il,as,optimizeExpr e)) defs)

optimizeProgram :: [MonoProgram -> MonoProgram] -> MonoProgram -> MonoProgram
optimizeProgram passes p = foldl (flip ($)) p passes
