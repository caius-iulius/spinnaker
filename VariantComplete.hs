module VariantComplete where
import HLDefs
import TypingDefs
import TypeTyper(getVariantData)

completeVariant :: TypingEnv -> HLExpr -> TyperState HLExpr
completeVariant _ e@(_, _, ExprLiteral _) = return e
completeVariant env (c, t, ExprApp e0 e1) = do
    e0' <- completeVariant env e0
    e1' <- completeVariant env e1
    return (c, t, ExprApp e0' e1')
completeVariant _ e@(_, _, ExprLabel _) = return e
completeVariant env (c, t, ExprConstructor l es) = do
    VariantData _ vqs vts vt <- getVariantData c env l
    zerotoadde <- return [0..length vts - length es -1]
    addesuffixes <- mapM (\_->newUniqueSuffix) zerotoadde
    return $ let
            addenames = map ("_v"++) addesuffixes
            addees = map (\myl -> (c, DataNOTHING, ExprLabel myl)) addenames
        in foldr (\myl e -> (c, DataNOTHING, ExprLambda (c, Just myl, PatWildcard) e)) (c, DataNOTHING, ExprConstructor l (es ++ addees)) addenames
completeVariant env (c, t, ExprLambda p e) = do
    e' <- completeVariant env e
    return (c, t, ExprLambda p e')
completeVariant env (c, t, ExprPut v pses) = do
    v' <- completeVariant env v
    pses' <- mapM (\(p, e)-> completeVariant env e >>= \e' -> return (p, e')) pses
    return (c, t, ExprPut v' pses')

completeVariantProgram env (BlockProgram datadefs valdefs) = do
    valdefs' <- mapM (mapM (\(ValDef c l t e)-> completeVariant env e >>= (return . ValDef c l t))) valdefs
    return (BlockProgram datadefs valdefs')
