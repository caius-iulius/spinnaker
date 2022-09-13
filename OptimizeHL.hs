module OptimizeHL where
import HLDefs
import Data.Char (ord, chr)
import Data.List (sortBy)

type Definitions = [(String, HLExpr)]
type Program = (HLExpr, Definitions)

appearsPatInner l PatWildcard = False
appearsPatInner l (PatLiteral _) = False
appearsPatInner l (PatVariant c ps) = any (appearsPat l) ps

appearsPat :: String -> HLPattern -> Bool
appearsPat l (_, Nothing, ip) = appearsPatInner l ip
appearsPat l (_, Just l', _) = l == l'
appears :: String -> HLExpr -> Int
appears _ (_, _, ExprLiteral _) = 0
appears l (_, _, ExprApp f a) = appears l f + appears l a
appears l (_, _, ExprLabel l') = if l == l' then 1 else 0
appears l (_, _, ExprConstructor c es) = sum (map (appears l) es)
appears l (_, _, ExprCombinator c es) = sum (map (appears l) es)
appears l (_, _, ExprLambda p e) = if appearsPat l p then 0 else appears l e
appears l (_, _, ExprPut vs pses) = sum (map (appears l) vs) +
    sum (map (\(ps, e)->if any (appearsPat l) ps then 0 else appears l e) pses)

appearsDefs :: String -> Definitions -> Int
appearsDefs l defs = sum $ map (appears l . snd) defs

exprSize :: HLExpr -> Int
exprSize (_, _, ExprLiteral _) = 1
exprSize (_, _, ExprApp f a) = exprSize f + exprSize a --TODO: +1?
exprSize (_, _, ExprLabel _) = 1
exprSize (_, _, ExprConstructor _ es) = 1 + sum (map exprSize es)
exprSize (_, _, ExprCombinator _ es) = 1 + sum (map exprSize es)
exprSize (_, _, ExprLambda p e) = 1 + exprSize e --TODO patSize p?
exprSize (_, _, ExprPut vs pses) = length pses + sum (map exprSize vs) + sum (map (exprSize . snd) pses) --TODO patsize pses?
exprSize (_, _, ExprHint _ e) = exprSize e

programSize :: Program -> Int
programSize (ep, defs) = exprSize ep + sum (map (exprSize . snd) defs)

inlineHeuristic :: HLExpr -> Int -> Bool
inlineHeuristic e appears =
    let size = exprSize e
        addedSize = size*(appears - 1) - 1
    in size < 8 || addedSize <= (2*size)

inline :: String -> HLExpr -> HLExpr -> HLExpr
inline l ie e@(_, _, ExprLiteral _) = e
inline l ie e@(_, _, ExprLabel l')
    | l == l' = ie
    | otherwise = e
inline l ie (c, t, ExprApp f a) = (c, t, ExprApp (inline l ie f) (inline l ie a))
inline l ie (c, t, ExprConstructor cn es) = (c, t, ExprConstructor cn (map (inline l ie) es))
inline l ie (c, t, ExprCombinator cn es) = (c, t, ExprCombinator cn (map (inline l ie) es))
inline l ie e@(c, t, ExprLambda p le)
    | appearsPat l p = e
    | otherwise = (c, t, ExprLambda p (inline l ie le))
inline l ie (c, t, ExprPut vs pses) = (c, t, ExprPut (map (inline l ie) vs)
    (map (\(p, e)->if any (appearsPat l) p then (p, e) else (p, inline l ie e)) pses))

-- TODO: Inline più furbo, per esempio dai la precedenza alle definizioni che appaiono di meno
sortInlines :: Program -> Program
sortInlines (ep, defs) =
    (ep, sortBy (\(l,e) (l',e')->
        compare (appears l ep + appearsDefs l defs) (appears l' ep + appearsDefs l' defs)
    ) defs)

inlineProgram :: Program -> Program
inlineProgram prog = loop [] (sortInlines prog)
    where
        loop procd (ep, []) = (ep, procd)
        loop procd (ep, (l, e):defs)
            | (appears l ep + appearsDefs l (procd ++ defs)) == 0
                = loop procd (ep, defs)
            | appears l e /= 0 || not (inlineHeuristic e (appears l ep + appearsDefs l (procd++defs)))
                = loop ((l,e):procd) (ep, defs)
            | otherwise = loop (inlineDefs l e procd) (inline l e ep, inlineDefs l e defs)
        inlineDefs l ie [] = []
        inlineDefs l ie ((ld, e):defs') = (ld, inline l ie e):inlineDefs l ie defs'
--     where
--         loop myep procd [] = (myep, procd)
--         loop myep procd ((l, e):defs')
--             | (appears l myep + appearsDefs l (procd ++ defs')) == 0
--                 = loop myep procd defs'
--             | appears l e /= 0 || not (inlineHeuristic e (appears l myep + appearsDefs l procd + appearsDefs l defs'))
--                 = loop myep ((l, e):procd) defs'
--             | otherwise = loop (inline l e myep) (inlineDefs l e procd) (inlineDefs l e defs')
--         inlineDefs l ie [] = []
--         inlineDefs l ie ((ld, e):defs') = (ld, inline l ie e):inlineDefs l ie defs'

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

optimizeBI c t "_addInt" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[]) = (c, t, ExprLiteral (LitInteger (i0+i1)))
optimizeBI c t "_subInt" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[]) = (c, t, ExprLiteral (LitInteger (i0-i1)))
optimizeBI c t "_mulInt" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[]) = (c, t, ExprLiteral (LitInteger (i0*i1)))
optimizeBI c t "_divInt" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[]) = (c, t, ExprLiteral (LitInteger (div i0 i1)))
optimizeBI c t "_equInt" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[]) = (c, t, ExprConstructor (if i0 == i1 then "True#BI" else "False#BI") [])
optimizeBI c t "_neqInt" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[]) = (c, t, ExprConstructor (if i0 /= i1 then "True#BI" else "False#BI") [])
optimizeBI c t "_leqInt" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[]) = (c, t, ExprConstructor (if i0 <= i1 then "True#BI" else "False#BI") [])
optimizeBI c t "_greInt" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[]) = (c, t, ExprConstructor (if i0 > i1 then "True#BI" else "False#BI") [])
optimizeBI c t "_convItoC" ((_, _, ExprLiteral (LitInteger i)):[]) = (c, t, ExprLiteral (LitCharacter (chr i)))
optimizeBI c t "_convCtoI" ((_, _, ExprLiteral (LitCharacter ch)):[]) = (c, t, ExprLiteral (LitInteger (ord ch)))
optimizeBI c t l es = (c, t, ExprCombinator l es)

optimizeExpr :: HLExpr -> HLExpr
optimizeExpr e@(_, _, ExprLiteral _) = e
optimizeExpr (c, t, ExprApp f a) =
    let f' = optimizeExpr f
        a' = optimizeExpr a
    in case f' of
        (_, _, ExprLambda pat inner) -> optimizeExpr (c, t, ExprPut [a'] [([pat], inner)])
        _ -> (c, t, ExprApp f' a')
optimizeExpr e@(_, _, ExprLabel _) = e
optimizeExpr (c, t, ExprConstructor l es) = (c, t, ExprConstructor l (map optimizeExpr es))
optimizeExpr (c, t, ExprCombinator l es) = optimizeBI c t l (map optimizeExpr es)
optimizeExpr (c, t, ExprPut vals pses) = --TODO: putofput
    let vals' = map optimizeExpr vals
        pses' = sievePatterns vals' pses
        pses'' = map (\(p,e)->(p,optimizeExpr e)) pses'
    in case pses'' of
        (p, e):[] -> case sievePatternList p vals' of
            Always bs -> 
                if all (\(ml,me)->inlineHeuristic me (appears ml e)) bs
                then optimizeExpr $
                    --TODO: questo effettua un inline forse troppo permissivo
                    foldl (\me (l,e')->inline l e' me) e bs
                else (c, t, ExprPut vals' pses'')
            _ -> (c, t, ExprPut vals' pses'')
        _ -> (c, t, ExprPut vals' pses'')
        --error $ "OPTIMIZED val " ++ show val' ++ "\npses " ++ show pses ++ "\npses'" ++ show pses'
optimizeExpr (c, t, ExprLambda pat e) = (c, t, ExprLambda pat (optimizeExpr e))
optimizeExpr (_, _, ExprHint _ e) = optimizeExpr e

optimizeProgram :: Program -> Program
optimizeProgram p =
    let p' = optimizeDefExprs p
        p'' = inlineProgram p'
        p''' = optimizeDefExprs p''
    in p''' -- inlineProgram p'''
    where optimizeDefExprs (ep, defs) = (optimizeExpr ep,
            map (\(l,e)->(l,optimizeExpr e)) defs)
