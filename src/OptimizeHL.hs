module OptimizeHL where
import Data.Char (ord, chr)
import Data.List (sortBy)
import Data.Maybe(fromMaybe)

import HLDefs
import Typer.TypingDefs

appearsPatInner l PatWildcard = False
appearsPatInner l (PatLiteral _) = False
appearsPatInner l (PatVariant c ps) = any (appearsPat l) ps

appearsPat :: String -> HLPattern -> Bool
appearsPat l (_, ml, ip) = Just l == ml || appearsPatInner l ip

appears :: String -> HLExpr -> Int
appears _ (_, _, ExprLiteral _) = 0
appears l (_, _, ExprApp f a) = appears l f + appears l a
appears l (_, _, ExprLabel l') = if l == l' then 1 else 0
appears l (_, _, ExprConstructor c es) = sum (map (appears l) es)
appears l (_, _, ExprCombinator c es) = (if c == l then 1 else 0) + sum (map (appears l) es)
appears l (_, _, ExprLambda l' e) = if l == l' then 0 else appears l e
appears l (_, _, ExprPut vs pses) = sum (map (appears l) vs) +
    sum (map (\(ps, e)->if any (appearsPat l) ps then 0 else appears l e) pses)

appearsDefs :: String -> [Combinator] -> Int
appearsDefs l defs = sum $ map (\(_,_,as,e) -> if elem l (map fst as) then 0 else appears l e) defs

exprSize :: HLExpr -> Int
exprSize (_, _, ExprLiteral _) = 1
exprSize (_, _, ExprApp f a) = exprSize f + exprSize a --TODO: +1?
exprSize (_, _, ExprLabel _) = 1
exprSize (_, _, ExprConstructor _ es) = 1 + sum (map exprSize es)
exprSize (_, _, ExprCombinator _ es) = 1 + sum (map exprSize es)
exprSize (_, _, ExprLambda p e) = 1 + exprSize e --TODO patSize p?
exprSize (_, _, ExprPut vs pses) = length pses + sum (map exprSize vs) + sum (map (exprSize . snd) pses) --TODO patsize pses?
exprSize (_, _, ExprHint _ e) = exprSize e

programSize :: MonoProgram -> Int
programSize (ep, defs) = exprSize ep + sum (map (exprSize . (\(_,_,_,a)->a)) defs)

inlineHeuristic :: HLExpr -> Int -> Bool
inlineHeuristic e appears =
    let size = exprSize e
        addedSize = size*(appears - 1)
    in size < 8 || addedSize < size

inline :: [(String, HLExpr)] -> HLExpr -> HLExpr
inline binds e@(_, _, ExprLiteral _) = e
inline binds e@(c, _, ExprLabel l') = fromMaybe e (lookup l' binds)
inline binds (c, t, ExprApp f a) = (c, t, ExprApp (inline binds f) (inline binds a))
inline binds (c, t, ExprConstructor cn es) = (c, t, ExprConstructor cn (map (inline binds) es))
inline binds (c, t, ExprCombinator cn es) = (c, t, ExprCombinator cn (map (inline binds) es))
inline binds (c, t, ExprLambda l' le) =
    let newbinds = filter ((l' /=) . fst) binds
        in (c, t, ExprLambda l' (inline newbinds le))
inline binds (c, t, ExprPut vs pses) = (c, t, ExprPut (map (inline binds) vs)
    (map (\(p, e)->
        let newbinds = filter (\(sl, _) -> not $ any (appearsPat sl) p) binds
            in (p, inline binds e)) pses))

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
-- (c, t, ExprCombinator cn (map (inlineComb cmb) es))
inlineComb cmb e@(c, t, ExprLambda l' le) = (c, t, ExprLambda l' (inlineComb cmb le))
inlineComb cmb (c, t, ExprPut vs pses) = (c, t, ExprPut (map (inlineComb cmb) vs)
    (map (\(p, e)-> (p, inlineComb cmb e)) pses))

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

        inlineDefs cmb [] = []
        inlineDefs cmb ((ld, il, as, e):defs') = (ld, il, as, inlineComb cmb e):inlineDefs cmb defs'

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

optimizeProgram :: MonoProgram -> MonoProgram
optimizeProgram p =
    let p' = optimizeDefExprs p
        p'' = inlineProgram p'
        p''' = optimizeDefExprs p''
    in p''' -- inlineProgram p'''
    where optimizeDefExprs (ep, defs) = (optimizeExpr ep,
            map (\(l,il,as,e)->(l,il,as,optimizeExpr e)) defs)
