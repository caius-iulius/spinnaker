module OptimizeHL where
import HLDefs

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
exprSize (_, _, ExprConstructor _ es) = sum $ map exprSize es --TODO: +1?
exprSize (_, _, ExprLambda p e) = 1 + exprSize e --TODO patSize p?
exprSize (_, _, ExprPut v pses) = length pses + exprSize v + sum (map (exprSize . snd) pses) --TODO patsize pses?

inlineHeuristic :: HLExpr -> Int -> Bool
inlineHeuristic e appears =
    let size = exprSize e
        addedSize = size*(appears - 1) - 1
    in size < 8 || addedSize < size

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
