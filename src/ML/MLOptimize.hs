module ML.MLOptimize where
import MLDefs
import ML.MLOps

optimizeMLExpr :: MLExpr -> MLExpr
optimizeMLExpr e@(_, _, MLLiteral _) = e
optimizeMLExpr e@(_, _, MLLabel _) = e
optimizeMLExpr e@(_, _, MLProj _ _ _ _) = e
optimizeMLExpr e@(_, _, MLError _ _) = e
optimizeMLExpr (c, t, MLConstructor v es) = (c, t, MLConstructor v $ map optimizeMLExpr es)
optimizeMLExpr (c, t, MLCombinator v es) = (c, t, MLCombinator v $ map optimizeMLExpr es)
optimizeMLExpr (c, t, MLTest l ty pes def) = (c, t, MLTest l ty (map (\(p, e) -> (p, optimizeMLExpr e)) pes) (optimizeMLExpr def))
optimizeMLExpr (c, t, MLLet l (_, _, MLLabel l') e1) = mllabsubst l l' $ optimizeMLExpr e1
optimizeMLExpr (c, t, MLLet l e0 e1) = let e1' = optimizeMLExpr e1 in
    --if mlappears l e1' == 0 then e1' else
    (c, t, MLLet l (optimizeMLExpr e0) e1')
    --TODO: sostituzione di un'espressione usata una sola volta

optimizeMLProg :: MLProgram -> MLProgram
optimizeMLProg (ep, defs) =
    (optimizeMLExpr ep, map optimizeDef defs)
    where optimizeDef (lab, args, expr) = (lab, args, optimizeMLExpr expr)
