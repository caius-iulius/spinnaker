module VariantComplete(completeVariantValDefGroups, completeVariantInstDefs) where
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
    es' <- mapM (completeVariant env) es
    VariantData _ vqs vts vt <- getVariantData env l
    let zerotoadde = [0..length vts - length es -1]
    addesuffixes <- mapM (\_->newUniqueSuffix) zerotoadde
    return $ let
            addenames = map ("_v"++) addesuffixes
            addees = map (\myl -> (c, DataNOTHING, ExprLabel myl)) addenames
        in foldr (\myl e -> (c, DataNOTHING, ExprLambda myl e)) (c, DataNOTHING, ExprConstructor l (es' ++ addees)) addenames
completeVariant env (c, t, ExprCombinator l es) = do
    es' <- mapM (completeVariant env) es
    return (c, t, ExprCombinator l es')
completeVariant env (c, t, ExprLambda l e) = do
    e' <- completeVariant env e
    return (c, t, ExprLambda l e')
completeVariant env (c, t, ExprPut vs pses) = do
    vs' <- mapM (completeVariant env) vs
    pses' <- mapM (\(p, e)-> completeVariant env e >>= \e' -> return (p, e')) pses
    return (c, t, ExprPut vs' pses')
completeVariant env (c, t, ExprHint hint e) = do
    e' <- completeVariant env e
    return (c, t, ExprHint hint e')

completeVariantValDefGroups :: TypingEnv -> [[HLValDef]] -> TyperState [[HLValDef]]
completeVariantValDefGroups env = mapM (mapM (\(ValDef c l t ps e)-> completeVariant env e >>= (return . ValDef c l t ps)))

completeVariantInstDefs :: TypingEnv -> [HLInstDef] -> TyperState [HLInstDef]
completeVariantInstDefs env =
    mapM (\(InstDef c qh defs)->(mapM (\(c', l, e)-> do
        e' <- completeVariant env e
        return (c', l, e')) defs) >>= return . InstDef c qh)
