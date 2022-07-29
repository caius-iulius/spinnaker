module OptimizeHL where
import HLDefs
import Data.Char (ord, chr)

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
appears l (_, _, ExprLambda p e) = if appearsPat l p then 0 else appears l e
appears l (_, _, ExprPut v pses) = appears l v +
    sum (map (\(p, e)->if appearsPat l p then 0 else appears l e) pses)

appearsDefs :: String -> Definitions -> Int
appearsDefs l defs = sum $ map (appears l . snd) defs

exprSize :: HLExpr -> Int
exprSize (_, _, ExprLiteral _) = 1
exprSize (_, _, ExprApp f a) = exprSize f + exprSize a --TODO: +1?
exprSize (_, _, ExprLabel _) = 1
exprSize (_, _, ExprConstructor _ es) = 1 + sum (map exprSize es)
exprSize (_, _, ExprLambda p e) = 1 + exprSize e --TODO patSize p?
exprSize (_, _, ExprPut v pses) = length pses + exprSize v + sum (map (exprSize . snd) pses) --TODO patsize pses?

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
inline l ie e@(c, t, ExprLambda p le)
    | appearsPat l p = e
    | otherwise = (c, t, ExprLambda p (inline l ie le))
inline l ie (c, t, ExprPut v pses) = (c, t, ExprPut (inline l ie v)
    (map (\(p, e)->if appearsPat l p then (p, e) else (p, inline l ie e)) pses))

-- TODO: Inline più furbo, per esempio dai la precedenza alle definizioni che appaiono di meno
inlineProgram :: Program -> Program
inlineProgram (ep, defs) = loop ep [] defs
    where
        loop myep procd [] = (myep, procd)
        loop myep procd ((l, e):defs')
            | appears l e /= 0 || not (inlineHeuristic e (appears l myep + appearsDefs l procd + appearsDefs l defs'))
                = loop myep ((l, e):procd) defs'
            | otherwise = loop (inline l e myep) (inlineDefs l e procd) (inlineDefs l e defs')
        inlineDefs l ie [] = []
        inlineDefs l ie ((ld, e):defs') = (ld, inline l ie e):inlineDefs l ie defs'

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
    if pvar == evar then
        let maps = zipWith sievePattern ps es
            in concatRess maps
    else Never
sievePatternInner p e = Maybe

sievePattern :: HLPattern -> HLExpr -> SieveRes
sievePattern (_, Nothing, patdata) e = sievePatternInner patdata e
sievePattern (_, Just l, patdata) e =
    let inner = sievePatternInner patdata e
        in concatRess [Always[(l, e)],inner]

sievePatterns :: HLExpr -> [(HLPattern, HLExpr)] -> [(HLPattern, HLExpr)]
sievePatterns v = reverse . loop []
    where loop pses' [] = pses'
          loop pses' ((p, e):pses) =
            case sievePattern p v of
                Always _ -> (p, e):pses'
                Maybe -> loop ((p, e):pses') pses
                Never -> loop pses' pses

optimizeBI c t (_, _, ExprLabel "_addInt#EXT") (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = (c, t, ExprLiteral (LitInteger (i0+i1)))
optimizeBI c t (_, _, ExprLabel "_subInt#EXT") (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = (c, t, ExprLiteral (LitInteger (i0-i1)))
optimizeBI c t (_, _, ExprLabel "_mulInt#EXT") (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = (c, t, ExprLiteral (LitInteger (i0*i1)))
optimizeBI c t (_, _, ExprLabel "_divInt#EXT") (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = (c, t, ExprLiteral (LitInteger (div i0 i1)))
optimizeBI c t (_, _, ExprLabel "_equInt#EXT") (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = (c, t, ExprConstructor (if i0 == i1 then "True#BI" else "False#BI") [])
optimizeBI c t (_, _, ExprLabel "_neqInt#EXT") (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = (c, t, ExprConstructor (if i0 /= i1 then "True#BI" else "False#BI") [])
optimizeBI c t (_, _, ExprLabel "_leqInt#EXT") (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = (c, t, ExprConstructor (if i0 <= i1 then "True#BI" else "False#BI") [])
optimizeBI c t (_, _, ExprLabel "_greInt#EXT") (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = (c, t, ExprConstructor (if i0 > i1 then "True#BI" else "False#BI") [])
optimizeBI c t (_, _, ExprLabel "_convItoC#EXT") (_, _, ExprLiteral (LitInteger i)) = (c, t, ExprLiteral (LitCharacter (chr i)))
optimizeBI c t (_, _, ExprLabel "_convCtoI#EXT") (_, _, ExprLiteral (LitCharacter ch)) = (c, t, ExprLiteral (LitInteger (ord ch)))
optimizeBI c t f a = (c, t, ExprApp f a)

optimizeExpr :: HLExpr -> HLExpr
optimizeExpr e@(_, _, ExprLiteral _) = e
optimizeExpr (c, t, ExprApp f a) =
    let f' = optimizeExpr f
        a' = optimizeExpr a
    in case f' of
        (_, _, ExprLambda pat inner) -> optimizeExpr (c, t, ExprPut a' [(pat, inner)])
        _ -> optimizeBI c t f' a'
optimizeExpr e@(_, _, ExprLabel _) = e
optimizeExpr (c, t, ExprConstructor l es) = (c, t, ExprConstructor l (map optimizeExpr es))
optimizeExpr (c, t, ExprPut val pses) = --TODO: putofput
    let val' = optimizeExpr val
        pses' = sievePatterns val' pses
        pses'' = map (\(p,e)->(p,optimizeExpr e)) pses'
    in case pses'' of
        (p, e):[] -> case sievePattern p val' of
            Always bs -> optimizeExpr $
                --TODO: questo effettua inline con qualsiasi espressione che appare un qualsiasi numero di volte, fa esplodere la dimensione
                foldl (\me (l,e')->inline l e' me) e bs
            _ -> (c, t, ExprPut val' pses'')
        _ -> (c, t, ExprPut val' pses'')
        --error $ "OPTIMIZED val " ++ show val' ++ "\npses " ++ show pses ++ "\npses'" ++ show pses'
optimizeExpr (c, t, ExprLambda pat e) = (c, t, ExprLambda pat (optimizeExpr e))

optimizeProgram :: Program -> Program
optimizeProgram p =
    let p' = optimizeDefExprs $! p
        p'' = inlineProgram $! p'
        p''' = optimizeDefExprs $! p''
    in p'''
    where optimizeDefExprs (ep, defs) = (optimizeExpr ep,
            map (\(l,e)->(l,optimizeExpr e)) defs)
