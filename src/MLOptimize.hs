module MLOptimize where
import MLDefs
import MLOps

optimizeMLExpr (c, t, MLLiteral l) = (c, t, MLLiteral l)
optimizeMLExpr (c, t, MLLabel l) = (c, t, MLLabel l)
optimizeMLExpr (c, t, MLConstructor v es) = (c, t, MLConstructor v $ map optimizeMLExpr es)
optimizeMLExpr (c, t, MLCombinator v es) = (c, t, MLCombinator v $ map optimizeMLExpr es)
optimizeMLExpr (c, t, MLTest l p e0 e1) = (c, t, MLTest l p (optimizeMLExpr e0) (optimizeMLExpr e1))
optimizeMLExpr (c, t, MLLet l (_, _, MLLabel l') e1) = mllabsubst l l' $ optimizeMLExpr e1
optimizeMLExpr (c, t, MLLet l e0 e1) = (c, t, MLLet l (optimizeMLExpr e0) (optimizeMLExpr e1))
optimizeMLExpr (c, t, MLError c' s) = (c, t, MLError c' s)

optimizeMLProg (ep, defs) =
    (optimizeMLExpr ep, map optimizeDef defs)
    where optimizeDef (lab, args, expr) = (lab, args, optimizeMLExpr expr)
