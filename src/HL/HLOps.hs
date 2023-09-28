module HL.HLOps where
import Data.Maybe (isJust, maybeToList, fromMaybe)
import Typer.TypingDefs(DataType)
import HLDefs


patVarsInner PatWildcard = []
patVarsInner (PatLiteral _) = []
patVarsInner (PatVariant c ps) = ps >>= patVars

patVars :: HLPattern -> [(String, DataType)]
patVars (_, _, Nothing, ip) = patVarsInner ip
patVars (_, t, Just l, ip) = (l, t) : patVarsInner ip

appearsPat :: String -> HLPattern -> Bool
appearsPat l pat = isJust $ lookup l (patVars pat)

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
        --TODO: questo è un fix per evitare shadowing, significa che bisogna ristrutturare l'optimizer per creare nuove variabili uniche
        let newbinds = filter (\(sl, _) -> not $ any (appearsPat sl) p) binds in
            (p, inline newbinds e)) pses))

