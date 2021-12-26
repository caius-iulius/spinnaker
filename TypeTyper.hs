module TypeTyper where
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import TypingDefs
import MPCL (StdCoord)
import HIRDefs
import KindTyper(kind)

--Roba per le sostituzioni

type Subst = Map.Map TyQuant DataType

nullSubst :: Subst
nullSubst = Map.empty

composeSubst sa sb = Map.union (Map.map (substApply sa) sb) sa

quantBind :: StdCoord -> TyQuant -> DataType -> TyperState Subst
quantBind c q t
    | t == DataQuant q = return nullSubst
    | Set.member q (freetyvars t) = throwError $ show c ++ " Occurs check fails: " ++ show q ++ " into " ++ show t
    | kind q /= kind t = throwError $ show c ++ " Kinds do not match in substitution: " ++ show q ++ "into " ++ show t
    | otherwise = return (Map.singleton q t)

--Algoritmo MGU
{-
tupsMgu _ [] [] = return nullSubst
tupsMgu c (t:ts) (t':ts') = do
    s <- mgu c t t'
    s' <- tupsMgu c (map (substApply s) ts) (map (substApply s) ts')
    return $ composeSubst s' s
-}

tupsMgu :: StdCoord -> [(DataType, DataType)] -> TyperState Subst
tupsMgu c tts =
    foldl (\m_subst (dta, dtb) -> do{
        s <- m_subst;
        s' <- mgu c (substApply s dta) (substApply s dtb);
        return $ composeSubst s' s
    }) (return nullSubst) tts

mgu :: StdCoord -> DataType -> DataType -> TyperState Subst
mgu c (DataQuant q) t = quantBind c q t
mgu c t (DataQuant q) = quantBind c q t
mgu c (DataTuple dts) (DataTuple dts') =
    if length dts /= length dts' then throwError $ show c ++ " Could not unify tuples of different arity: " ++ show (DataTuple dts) ++ " and " ++ show (DataTuple dts')
    else tupsMgu c $ zip dts dts'
mgu c t@(DataTypeName s k) t'@(DataTypeName s' k') =
    if s == s'  && k == k' then return nullSubst else throwError $ show c ++ " Could not unify typenames: " ++ show t ++ " and " ++ show t'
mgu c (DataTypeApp f a) (DataTypeApp f' a') = do
    s <- mgu c f f'
    s' <- mgu c (substApply s a) (substApply s a')
    return (composeSubst s' s)
mgu c t t' =
    throwError $ show c ++ " Could not unify types: " ++ show t ++ " and " ++ show t'

-- Classe Types e altre funzioni utili

class Types t where
    freetyvars :: t -> Set.Set TyQuant
    substApply :: Subst -> t -> t

instance Types DataType where
    freetyvars (DataQuant q) = Set.singleton q
    freetyvars (DataTuple dts) = Set.unions $ map freetyvars dts
    freetyvars (DataTypeName _ _) = Set.empty
    freetyvars (DataTypeApp dta dtb) = Set.union (freetyvars dta) (freetyvars dtb)

    substApply s (DataQuant q) = case Map.lookup q s of
        Nothing -> DataQuant q
        Just t -> t
    substApply s (DataTuple dts) =
        DataTuple $ map (substApply s) dts
    substApply s (DataTypeApp dta dtb) =
        DataTypeApp (substApply s dta) (substApply s dtb)
    substApply s (DataTypeName tn k) = (DataTypeName tn k)

instance Types TyScheme where
    freetyvars (TyScheme qs dt) = Set.difference (freetyvars dt) (Set.fromList qs)
    substApply s (TyScheme qs dt) = TyScheme qs (substApply (foldr Map.delete s qs) dt)




--tyBindRemove (TypingEnv typeEnv kindEnv) labl = TypingEnv (Map.delete labl typeEnv) kindEnv

tyBindAdd :: StdCoord -> TypingEnv -> String -> TyScheme -> TyperState TypingEnv
tyBindAdd c (TypingEnv ts ks vs) labl scheme =
    case Map.lookup labl ts of
        Just _ -> throwError $ show c ++ " Variable already bound: " ++ labl
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
    nqs <- mapM (\(TyQuant _ k) -> freshType k) qs
    let subst = Map.fromList (zip qs nqs) in return $ substApply subst t


-- Funzioni di typing

buildFunType a r =
    DataTypeApp (DataTypeApp (DataTypeName "->" (KFun KStar (KFun KStar KStar))) a) r

typeLit :: Literal -> DataType
typeLit (LitInteger _) = DataTypeName "Int" KStar
typeLit (LitFloating _) = DataTypeName "Flt" KStar

-- Funzioni per i pattern, DA RICONTROLLARE E COMPLETARE
typePat :: Map.Map String [DataType] -> HIRPattern -> TyperState DataType
typePat _ (_, _, PatWildcard) = freshType KStar
typePat _ (_, _, PatLiteral lit) = return $ typeLit lit
typePat vs (_, _, PatTuple ps) = do
    ts <- mapM (typePat vs) ps
    return $ DataTuple ts
typePat vs (c, _, PatVariant v ps) = error "TODO Pattern variant typing"

{-patListPatVarsInEnv gf env [] [] = return env
patListPatVarsInEnv gf env (p:ps) (t:ts) = do
    env' <- patVarsInEnv gf env p t
    patListPatVarsInEnv gf env' ps ts
-}
--TODO Da testare
patListPatVarsInEnv gf env ps ts = foldl (\me (p, t)->do{e<-me; patVarsInEnv gf e p t}) (return env) (zip ps ts)


innerPatVarsInEnv _ _ env (PatWildcard) dt = return env
innerPatVarsInEnv _ _ env (PatLiteral _) dt = return env
innerPatVarsInEnv gf c env (PatTuple ps) (DataTuple ts) = patListPatVarsInEnv gf env ps ts
innerPatVarsInEnv gf c env (PatVariant v ps) _ = error "TODO Pattern variant innerPatVarsInEnv"

patVarsInEnv :: (DataType -> TyScheme) -> TypingEnv -> HIRPattern -> DataType -> TyperState TypingEnv
patVarsInEnv gf env (c, Nothing, pdata) dt = innerPatVarsInEnv gf c env pdata dt
patVarsInEnv gf env (c, Just labl, pdata) dt = do
    env' <- tyBindAdd c env labl (gf dt)
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
    q <- freshType KStar
    (s1, t1, f') <- typeExpr env f
    (s2, t2, a') <- typeExpr (substApply s1 env) a
    s3 <- mgu c (substApply s2 t1) (buildFunType t2 q)
    lift $ lift $ putStrLn $ show c ++" TypingApp s:" ++ show (composeSubst s3 (composeSubst s2 s1)) ++ " Call:" ++ show t1 ++ " with:" ++ show t2
    let finals = composeSubst s3 (composeSubst s2 s1)
        finalt = substApply finals q
    return (finals, finalt, (c, finalt, ExprFCall f' a'))
-- TODO: Da qui in poi controllare bene, non so se è giusto
typeExpr env (c, _, ExprTuple exprs) =
    let typeExprsInternal _ ([]) = return (nullSubst, [], [])
        typeExprsInternal env' (e:es) = do
            (s, dt, e') <- typeExpr env' e
            (s', dts, es') <- typeExprsInternal (substApply s env') es
            return (composeSubst s' s, substApply s' dt : dts, e' : es')
    in do
        (s, dts, finalexprs) <- typeExprsInternal env exprs
        return (s, DataTuple dts, (c, DataTuple dts, ExprTuple finalexprs))
typeExpr env@(TypingEnv _ _ vs) (c, _, ExprLambda pat expr) = do
    argt <- typePat vs pat
    env' <- patVarsInEnv (TyScheme []) env pat argt
    (s, t, e) <- typeExpr env' expr
    let finaldt = buildFunType (substApply s argt) t
        in return (s, finaldt, (c, finaldt, ExprLambda pat e))
typeExpr env (c, _, ExprPut val pses) = do
    (s, tval, val') <- typeExpr env val
    (s', tval') <- unifyPats (substApply s env) tval pses
    tempt <- freshType KStar--TODO GIUSTO IL FRESH?
    (s'', texpr, pses') <- typePutBranches (substApply (composeSubst s' s) env) tval' tempt pses
    return (composeSubst s'' (composeSubst s' s), texpr, (c, texpr, ExprPut val' pses'))

--Funzioni helper per putexpr
unifyPats :: TypingEnv -> DataType -> [(HIRPattern, HIRExpr)] -> TyperState (Subst, DataType)
unifyPats _ t [] = return (nullSubst, t)
unifyPats env@(TypingEnv _ _ vs) t ((pat, (c, _, _)):branches) = do
    tpat <- typePat vs pat
    s <- mgu c t tpat
    (s', t') <- unifyPats (substApply s env) (substApply s t) branches
    return (composeSubst s' s, t')

typePutBranches :: TypingEnv -> DataType -> DataType -> [(HIRPattern, HIRExpr)] -> TyperState (Subst, DataType, [(HIRPattern, HIRExpr)])
typePutBranches _ _ texpr [] = return (nullSubst, texpr, [])
typePutBranches env tpat texpr ((pat, expr@(c, _, _)):branches) = do
    env' <- patVarsInEnv (generalize env) env pat tpat
    (s, texpr', expr') <- typeExpr env' expr
    s' <- mgu c texpr texpr'
    mys <- return $ composeSubst s' s
    (s'', tfinal, others) <- typePutBranches (substApply mys env) tpat (substApply s' texpr) branches
    return (composeSubst s'' mys, tfinal, (pat, expr'):others)

--Sostituzioni su espressioni e definizioni, eseguite solo nel toplevel (riduci ancora il numero di applicazioni)
substApplyExpr :: Subst -> HIRExpr -> HIRExpr
substApplyExpr s (c, dt, ExprLiteral l) = (c, substApply s dt, ExprLiteral l)
substApplyExpr s (c, dt, ExprFCall f a) = (c, substApply s dt, ExprFCall (substApplyExpr s f) (substApplyExpr s a))
substApplyExpr s (c, dt, ExprLabel l) = (c, substApply s dt, ExprLabel l)
substApplyExpr s (c, dt, ExprTuple es) = (c, substApply s dt, ExprTuple $ map (substApplyExpr s) es)
substApplyExpr s (c, dt, ExprLambda p e) = (c, substApply s dt, ExprLambda p (substApplyExpr s e))
substApplyExpr s (c, dt, ExprPut v psandes) = (c, substApply s dt, ExprPut (substApplyExpr s v) (map (\(p, e) -> (p, substApplyExpr s e)) psandes))

substApplyValDef s (ValDef c l e) = ValDef c l (substApplyExpr s e)

--Funzioni per le definizioni globali
typeValDef env (ValDef c l e) = do
    (s, dt, e') <- typeExpr env e
    lift $ lift $ putStrLn $ "typed valdef: " ++ l ++ " with type: " ++ show dt ++ " and subst: " ++ show s
    return (s, ValDef c l e')

quantifiedValDefEnv init_env [] = return init_env
quantifiedValDefEnv env (ValDef c s _:vdefs) = do
    t <- freshType KStar
    env' <- tyBindAdd c env s (TyScheme [] t)
    quantifiedValDefEnv env' vdefs

typeValDefsLoop _ [] = return (nullSubst, [])
typeValDefsLoop env (vdef:vdefs) = do
    (s, vdef') <- typeValDef env vdef
    (s', vdefs') <- typeValDefsLoop (substApply s env) vdefs
    return (composeSubst s' s, vdef':vdefs')

{-addValDefsEnv env [] = return env
addValDefsEnv env (ValDef c l (_, t, _):vdefs) = do
    env' <- tyBindAdd c env l (generalize env t)
    addValDefsEnv env' vdefs-}
addValDefsEnv env vdefs = foldl (\me (ValDef c l (_, t, _))->do{e<-me; tyBindAdd c e l (generalize e t)}) (return env) vdefs

unionValDefEnv (TypingEnv ts _ _) (ValDef c l (_, t, _)) = do
    tFromEnv <- case Map.lookup l ts of
        Just scheme -> instantiate scheme
    s <- mgu c t tFromEnv
    lift $ lift $ putStrLn $ "union of env and vdef "++ l ++": " ++ show s
    return s

-- TODO: Quali di queste sostituzioni possono essere eliminate? (probabilmente quelle introdotte da typeValDefsLoop...)
typeValDefs env vdefs = do
    vars_env <- quantifiedValDefEnv env vdefs
    (s, vdefs') <- typeValDefsLoop vars_env vdefs
    substs <- mapM (unionValDefEnv (substApply s vars_env)) vdefs' -- Mi sa che questa cosa funziona solo perché le sostituzioni dovrebbero essere indipendenti l'una dall'altra a questo punto (cioè le due sostituzioni non contengono frecce discordanti e.g. q1->Int e q1->Flt) ... oppure è perché le sostituzioni vengono composte nel modo giusto???
    s' <- return $ foldl (flip composeSubst) s substs
    vdefs'' <- return $ map (substApplyValDef s') vdefs'
    env' <- addValDefsEnv (substApply s' env) vdefs''
    return (s', env', vdefs'')

typeValDefsGroups env [] = return (nullSubst, env, [])
typeValDefsGroups env (vdefs:vdefss) = do
    (s, env', vdefs') <- typeValDefs env vdefs --TODO: forse anche questa sostituzione dopo averla applicata al contesto può essere eliminata
    (s', env'', vdefss') <- typeValDefsGroups env' vdefss
    return (composeSubst s' s, env'', map (substApplyValDef s') vdefs':vdefss')
