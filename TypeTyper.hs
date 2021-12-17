module TypeTyper where
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import TypingDefs
import HIRDefs

--Roba per le sostituzioni

type Subst = Map.Map TyQuant DataType

nullSubst :: Subst
nullSubst = Map.empty

composeSubst sa sb = Map.union (Map.map (substApply sa) sb) sa

substApplyExpr :: Subst -> HIRExpr -> HIRExpr
substApplyExpr s (c, dt, ExprLiteral l) = (c, substApply s dt, ExprLiteral l)
substApplyExpr s (c, dt, ExprFCall f a) = (c, substApply s dt, ExprFCall (substApplyExpr s f) (substApplyExpr s a))
substApplyExpr s (c, dt, ExprLabel l) = (c, substApply s dt, ExprLabel l)
substApplyExpr s (c, dt, ExprTuple es) = (c, substApply s dt, ExprTuple $ map (substApplyExpr s) es)
substApplyExpr s (c, dt, ExprLambda p e) = (c, substApply s dt, ExprLambda p (substApplyExpr s e))
substApplyExpr s (c, dt, ExprPut v psandes) = (c, substApply s dt, ExprPut (substApplyExpr s v) (map (\(p, e) -> (p, substApplyExpr s e)) psandes))

quantBind :: TyQuant -> DataType -> TyperState Subst
quantBind q t
    | t == DataQuant q = return nullSubst
    | Set.member q (freetyvars t) = throwError $ "Occurs check fails: " ++ show (DataQuant q) ++ " into " ++ show t
    | otherwise = return (Map.singleton q t)

--Algoritmo MGU

tupsMgu [] [] = return nullSubst
tupsMgu (t:ts) (t':ts') = do
    s <- mgu t t'
    s' <- tupsMgu (map (substApply s) ts) (map (substApply s) ts')
    return $ composeSubst s' s

mgu :: DataType -> DataType -> TyperState Subst
mgu (DataQuant q) t = quantBind q t
mgu t (DataQuant q) = quantBind q t
mgu (DataTuple dts) (DataTuple dts') =
    if length dts /= length dts' then throwError $ "Could not unify tuples of different arity: " ++ show (DataTuple dts) ++ " and " ++ show (DataTuple dts')
    else tupsMgu dts dts'
mgu (DataTypeName s) (DataTypeName s') =
    if s == s' then return nullSubst else throwError $ "Could not unify typenames: " ++ s ++ " and " ++ s'
mgu (DataTypeApp f a) (DataTypeApp f' a') = do
    s <- mgu f f'
    s' <- mgu (substApply s a) (substApply s a')
    return (composeSubst s s')
mgu t t' =
    throwError $ "Could not unify types: " ++ show t ++ " and " ++ show t'

-- Classe Types e altre funzioni utili

class Types t where
    freetyvars :: t -> Set.Set TyQuant
    substApply :: Subst -> t -> t

data TyScheme = TyScheme [TyQuant] DataType

instance Types DataType where
    -- freetyvars DataInt = Set.empty
    -- freetyvars DataFlt = Set.empty
    freetyvars (DataQuant q) = Set.singleton q
    freetyvars (DataTuple dts) = Set.unions $ map freetyvars dts
    freetyvars (DataTypeName _) = Set.empty
    freetyvars (DataTypeApp dta dtb) = Set.union (freetyvars dta) (freetyvars dtb)

    substApply s (DataQuant q) = case Map.lookup q s of
        Nothing -> DataQuant q
        Just t -> t
    substApply s (DataTuple dts) =
        DataTuple $ map (substApply s) dts
    substApply s (DataTypeApp dta dtb) =
        DataTypeApp (substApply s dta) (substApply s dtb)
    -- substApply s DataInt = DataInt
    -- substApply s DataFlt = DataFlt
    substApply s (DataTypeName tn) = (DataTypeName tn)

instance Types TyScheme where
    freetyvars (TyScheme qs dt) = Set.difference (freetyvars dt) (Set.fromList qs)
    substApply s (TyScheme qs dt) = TyScheme qs (substApply (foldr Map.delete s qs) dt)

-- contesto dei tipi (Types), specie (Kinds) e costruttori (Variants)
data TypingEnv = TypingEnv (Map.Map String TyScheme) (Map.Map String Kind) (Map.Map String [DataType])

--tyBindRemove (TypingEnv typeEnv kindEnv) labl = TypingEnv (Map.delete labl typeEnv) kindEnv

tyBindAdd :: TypingEnv -> String -> TyScheme -> TyperState TypingEnv
tyBindAdd (TypingEnv ts ks vs) labl scheme =
    case Map.lookup labl ts of
        Just _ -> throwError $ "Variable already bound: " ++ labl
        Nothing -> do
            return $ TypingEnv (Map.union ts (Map.singleton labl scheme)) ks vs

instance Types TypingEnv where
    freetyvars (TypingEnv ts ks vs) = Set.unions $ map freetyvars (Map.elems ts)
    substApply s (TypingEnv ts ks vs) = TypingEnv (Map.map (substApply s) ts) ks vs

generalize env t =
    let quants = Set.toList $ Set.difference (freetyvars t) (freetyvars env)
    in TyScheme quants t

instantiate :: TyScheme -> TyperState DataType
instantiate (TyScheme qs t) = do
    nqs <- mapM (\_ -> freshType) qs
    let subst = Map.fromList (zip qs nqs) in return $ substApply subst t


-- Funzioni di typing

buildFunType a r =
    DataTypeApp (DataTypeApp (DataTypeName "->") a) r

typeLit :: Literal -> DataType
typeLit (LitInteger _) = DataTypeName "Int"
typeLit (LitFloating _) = DataTypeName "Flt"

-- Funzioni per i pattern, DA RICONTROLLARE E COMPLETARE
typePat :: Map.Map String [DataType] -> HIRPattern -> TyperState DataType
typePat _ (_, _, PatWildcard) = freshType
typePat _ (_, _, PatLiteral lit) = return $ typeLit lit
typePat vs (_, _, PatTuple ps) = do
    ts <- mapM (typePat vs) ps
    return $ DataTuple ts
typePat vs (c, _, PatVariant v ps) = error "TODO Pattern variant typing"

patListPatVarsInEnv gf env [] [] = return env
patListPatVarsInEnv gf env (p:ps) (t:ts) = do
    env' <- patVarsInEnv gf env p t
    patListPatVarsInEnv gf env' ps ts

innerPatVarsInEnv _ _ env (PatWildcard) dt = return env
innerPatVarsInEnv _ _ env (PatLiteral _) dt = return env
innerPatVarsInEnv gf c env (PatTuple ps) (DataTuple ts) = patListPatVarsInEnv gf env ps ts
innerPatVarsInEnv gf c env (PatVariant v ps) _ = error "TODO Pattern variant innerPatVarsInEnv"

patVarsInEnv :: (DataType -> TyScheme) -> TypingEnv -> HIRPattern -> DataType -> TyperState TypingEnv
patVarsInEnv gf env (c, Nothing, pdata) dt = innerPatVarsInEnv gf c env pdata dt
patVarsInEnv gf env (c, Just labl, pdata) dt = do
    env' <- tyBindAdd env labl (gf dt)
    innerPatVarsInEnv gf c env' pdata dt

-- Funzioni per le espressioni
typeExpr :: TypingEnv -> HIRExpr -> TyperState (Subst, DataType, HIRExpr)
typeExpr _ (c, _, ExprLiteral lit) = do
    let dt = typeLit lit in return (nullSubst, dt, (c, dt, ExprLiteral lit))
typeExpr (TypingEnv env _ _) (c, _, ExprLabel labl) =
    case Map.lookup labl env of
        Nothing -> throwError $ show c ++ " Unbound variable: " ++ labl
        Just scheme -> do t <- instantiate scheme
                          return (nullSubst, t, (c, t, ExprLabel labl))
typeExpr env (c, _, ExprFCall f a) = do
    q <- freshType
    (s1, t1, f') <- typeExpr env f
    (s2, t2, a') <- typeExpr (substApply s1 env) a
    s3 <- mgu (substApply s2 t1) (buildFunType t2 q)
    let finals = composeSubst s3 (composeSubst s2 s1) in
        let finalt = substApply s3 q in
            return (finals, finalt, substApplyExpr finals (c, finalt, ExprFCall f' a'))
-- TODO: Da qui in poi controllare bene, non so se è giusto
typeExpr env (c, _, ExprTuple exprs) =
    let typeExprsInternal _ ([]) = return (nullSubst, [], [])
        typeExprsInternal env' (e:es) = do
            (s, dt, e') <- typeExpr env' e
            (s', dts, es') <- typeExprsInternal (substApply s env') es
            return (composeSubst s' s, substApply s' dt : dts, substApplyExpr s' e' : es')
    in do
        (s, dts, finalexprs) <- typeExprsInternal env exprs
        return (s, DataTuple dts, (c, DataTuple dts, ExprTuple finalexprs))
typeExpr env@(TypingEnv _ _ vs) (c, _, ExprLambda pat expr) = do
    argt <- typePat vs pat
    env' <- patVarsInEnv (TyScheme []) env pat argt
    (s, t, e) <- typeExpr env' expr
    let finaldt = buildFunType (substApply s argt) t
        in return (s, finaldt, (c, finaldt, ExprLambda pat e))
-- DA LIBRO ALGORITHM W, SECTION 2.2

-- TEMPORANEO
typeValDef env (ValDef c l e) = do
    (s, dt, e') <- typeExpr env e
    return $ ValDef c l e'
typeProgram (Program ddefs vdefs) = typeValDef (TypingEnv Map.empty Map.empty Map.empty) (head vdefs)
