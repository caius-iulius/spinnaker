module ML.MLOptimize where
import MLDefs
import ML.MLOps

optimizeMLExpr :: MLExpr -> MLExpr
optimizeMLExpr e@(_, _, MLLiteral _) = e
optimizeMLExpr e@(_, _, MLLabel _) = e
optimizeMLExpr e@(_, _, MLError _ _) = e
optimizeMLExpr (c, t, MLProj e var n) = (c, t, MLProj (optimizeMLExpr e) var n)
optimizeMLExpr (c, t, MLConstructor v es) = (c, t, MLConstructor v $ map optimizeMLExpr es)
optimizeMLExpr (c, t, MLCombinator v es) = (c, t, MLCombinator v $ map optimizeMLExpr es)
optimizeMLExpr (c, t, MLJoin j es) = (c, t, MLJoin j $ map optimizeMLExpr es)
optimizeMLExpr (c, t, MLTest tv pes def) = (c, t, MLTest (optimizeMLExpr tv) (map (\(p, e) -> (p, optimizeMLExpr e)) pes) (optimizeMLExpr def))
optimizeMLExpr (c, t, MLLet l e0@(_, _, MLLabel _) e1) = mlsubst l e0 $ optimizeMLExpr e1
optimizeMLExpr (c, t, MLLet l e0 e1) =
    let e0' = optimizeMLExpr e0
        e1' = optimizeMLExpr e1
    in case mlappears l e1' of
        0 -> e1'
        1 -> mlsubst l e0' e1'
        _ -> (c, t, MLLet l e0' e1')
    --TODO: sostituzione di un'espressione usata una sola volta
optimizeMLExpr (c, t, MLLetJoin j lts e0 e1) = 
    let e0' = optimizeMLExpr e0
        e1' = optimizeMLExpr e1
    in case mlappears j e1' of
        0 -> e1'
        1 -> joinsubst (j, map fst lts, e0') e1' --TODO: può capitare che e0' sia ottimizzato considerando che gli argomenti sono label, mentre quando viene inlinizzato possono non esserlo, basterebbe introdurre dei let in joinsubst e ottimizzare su quelli
        _ -> (c, t, MLLetJoin j lts e0' e1')
    --TODO: inline se è chiamato solo una volta

optimizeMLProg :: MLProgram -> MLProgram
optimizeMLProg (ep, defs) =
    (optimizeMLExpr ep, map optimizeDef defs)
    where optimizeDef (lab, args, expr) = (lab, args, optimizeMLExpr expr)
