module TypeTyper where
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import MPCL (StdCoord)
import TypingDefs
import HLDefs
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

-- Classe Types e altre funzioni utili

class Types t where
    freetyvars :: t -> Set.Set TyQuant
    substApply :: Subst -> t -> t

instance Types DataType where
    freetyvars (DataQuant q) = Set.singleton q
    freetyvars (DataTypeName _ _) = Set.empty
    freetyvars (DataTypeApp dta dtb) = Set.union (freetyvars dta) (freetyvars dtb)

    substApply s (DataQuant q) = case Map.lookup q s of
        Nothing -> DataQuant q
        Just t -> t
    substApply s (DataTypeApp dta dtb) =
        DataTypeApp (substApply s dta) (substApply s dtb)
    substApply s (DataTypeName tn k) = (DataTypeName tn k)

instance Types TyScheme where
    freetyvars (TyScheme qs dt) = Set.difference (freetyvars dt) (Set.fromList qs)
    substApply s (TyScheme qs dt) = TyScheme qs (substApply (foldr Map.delete s qs) dt)

--Algoritmo MGU
listMgu :: StdCoord -> [(DataType, DataType)] -> TyperState Subst
listMgu c tts =
    foldl (\m_subst (dta, dtb) -> do{
        s <- m_subst;
        s' <- mgu c (substApply s dta) (substApply s dtb);
        return $ composeSubst s' s
    }) (return nullSubst) tts

mgu :: StdCoord -> DataType -> DataType -> TyperState Subst
mgu c (DataQuant q) t = quantBind c q t
mgu c t (DataQuant q) = quantBind c q t
mgu c t@(DataTypeName s k) t'@(DataTypeName s' k') =
    if s == s'  && k == k' then return nullSubst else throwError $ show c ++ " Could not unify typenames: " ++ show t ++ " and " ++ show t'
mgu c (DataTypeApp f a) (DataTypeApp f' a') = do
    s <- mgu c f f'
    s' <- mgu c (substApply s a) (substApply s a')
    return (composeSubst s' s)
mgu c t t' =
    throwError $ show c ++ " Could not unify types: " ++ show t ++ " and " ++ show t'

{-
--TODO: Da testare
mergeInto c src tgt = do
    s <- mgu c src tgt
    let
        keyss = Set.fromList $ map fst $ Map.toList s
        frees = freetyvars tgt
        transformsInTgt = Set.intersection keyss frees
        in if length transformsInTgt /= 0
        then throwError $ show c ++ " Could not merge type: " ++ show src ++ " into: " ++ show tgt
        else return s
-}

--tyBindRemove (TypingEnv typeEnv kindEnv) labl = TypingEnv (Map.delete labl typeEnv) kindEnv
tyBindAdd :: StdCoord -> TypingEnv -> String -> TyScheme -> TypingEnv
tyBindAdd c (TypingEnv ts ks vs) labl scheme =
    case Map.lookup labl ts of
        --Just _ -> throwError $ show c ++ " Variable already bound: " ++ labl
        Nothing -> --do
            --lift $ lift $ putStrLn $ show c ++ " Binding variable: " ++ labl ++ ":" ++ show scheme
            --return $
            TypingEnv (Map.union ts (Map.singleton labl scheme)) ks vs

getVariantData :: StdCoord -> TypingEnv -> String -> TyperState VariantData
getVariantData _ _ l@('(':')':slen) =
    let len :: Int
        len = read slen
    in do
        qs <- mapM (\_->newTyQuant KType) [1..len]
        let ts = map DataQuant qs in return $ VariantData l qs ts (buildTupType ts)
getVariantData c (TypingEnv _ _ vs) l =
    case Map.lookup l vs of
        --Nothing -> throwError $ show c ++ " Unbound constructor: " ++ l
        Just vdata -> do
            lift $ lift $ putStrLn $ "VDATA " ++ show l ++ show vdata
            return vdata

instance Types TypingEnv where
    freetyvars (TypingEnv ts ks vs) = Set.unions $ map freetyvars (Map.elems ts)
    substApply s (TypingEnv ts ks vs) = TypingEnv (Map.map (substApply s) ts) ks vs

generalize env t =
    let quants = Set.toList $ Set.difference (freetyvars t) (freetyvars env)
    in TyScheme quants t

getInstantiationSubst qs = do
    nqs <- mapM (\(TyQuant _ k) -> freshType k) qs
    return $ Map.fromList (zip qs nqs)

instantiate :: TyScheme -> TyperState DataType
instantiate (TyScheme qs t) = do
    subst <- getInstantiationSubst qs
    return $ substApply subst t


-- Funzioni di typing
typeLit :: Literal -> DataType
typeLit (LitInteger _) = intT
typeLit (LitFloating _) = fltT

-- Funzioni per i pattern, DA RICONTROLLARE E COMPLETARE
typePat :: TypingEnv -> HLPattern -> TyperState DataType
typePat _ (_, _, PatWildcard) = freshType KType
typePat _ (_, _, PatLiteral lit) = return $ typeLit lit
typePat env (c, _, PatVariant v ps) = do
    (VariantData _ qs vts dt) <- getVariantData c env v
    if length ps /= length vts then throwError $ show c ++ " Constructor is applied to wrong number of arguments"
    else do
        s <- getInstantiationSubst qs
        pts <- mapM (typePat env) ps
        s' <- listMgu c $ zip (map (substApply s) vts) pts --TODO questo in teoria controlla la validità degli argomenti, va rifatto, forse serve un algoritmo di unificazione "one-way"
        lift $ lift $ putStrLn $ show c ++ " Variante:"++v++" di tipo-istanza:"++show (substApply s dt) ++ " unificato in:" ++ show (substApply s' (substApply s dt))
        return $ substApply s' $ substApply s dt

--TODO Da testare
patListPatVarsInEnv gf env ps ts = foldl (\me (p, t)->do{e<-me; patVarsInEnv gf e p t}) (return env) (zip ps ts)

innerPatVarsInEnv _ _ env (PatWildcard) dt = return env
innerPatVarsInEnv _ _ env (PatLiteral _) dt = return env
innerPatVarsInEnv gf c env (PatVariant v ps) dt = do
    (VariantData _ qs vts vdt) <- getVariantData c env v
    s <- mgu c vdt dt --TODO: Forse serve un algoritmo di unificazione "one-way"
    patListPatVarsInEnv gf env ps (map (substApply s) vts)

patVarsInEnv :: (DataType -> TyScheme) -> TypingEnv -> HLPattern -> DataType -> TyperState TypingEnv
patVarsInEnv gf env (c, Nothing, pdata) dt = innerPatVarsInEnv gf c env pdata dt
patVarsInEnv gf env (c, Just labl, pdata) dt =
    let env' = tyBindAdd c env labl (gf dt)
    in innerPatVarsInEnv gf c env' pdata dt

-- Funzioni per le espressioni
typeExpr :: TypingEnv -> HLExpr -> TyperState (Subst, DataType, HLExpr)
typeExpr _ (c, _, ExprLiteral lit) = do
    let dt = typeLit lit in return (nullSubst, dt, (c, dt, ExprLiteral lit))
typeExpr (TypingEnv env _ _) (c, _, ExprLabel labl) =
    case Map.lookup labl env of
        --Nothing -> throwError $ show c ++ " Unbound variable: " ++ labl
        Just scheme -> do
                          lift $ lift $ putStrLn $ show c ++ " LABEL:" ++ labl ++ " of scheme:" ++ show scheme
                          t <- instantiate scheme
                          return (nullSubst, t, (c, t, ExprLabel labl))
typeExpr env (c, _, ExprConstructor l []) = do
    (VariantData _ qs argts dt) <- getVariantData c env l
    s <- getInstantiationSubst qs
    let mydt = substApply s (foldr buildFunType dt argts)
    lift $ lift $ putStrLn $ "CONSTRUCTOR DT " ++ show l ++ show mydt
    return (nullSubst, mydt, (c, mydt, ExprConstructor l []))
typeExpr env (c, _, ExprConstructor l es) = do --TODO: Da testare
    (s, t, (_, _, ExprApp (_, _, ExprConstructor l' es') e')) <- typeExpr env (c, DataNOTHING, ExprApp (c, DataNOTHING, ExprConstructor l (init es)) (last es))
    return (s, t, (c, t, ExprConstructor l' (es' ++ [e'])))
    --typeExpr env (foldl (\e0 e1 -> (c, DataNOTHING, ExprApp e0 e1)) (c, DataNOTHING, ExprConstructor l []) es)
typeExpr env (c, _, ExprApp f a) = do
    q <- freshType KType
    (s1, t1, f') <- typeExpr env f
    (s2, t2, a') <- typeExpr (substApply s1 env) a
    s3 <- mgu c (substApply s2 t1) (buildFunType t2 q)
    -- lift $ lift $ putStrLn $ show c ++" TypingApp s:" ++ show (composeSubst s3 (composeSubst s2 s1)) ++ " Call:" ++ show t1 ++ " with:" ++ show t2
    let finals = composeSubst s3 (composeSubst s2 s1)
        finalt = substApply finals q
    return (finals, finalt, (c, finalt, ExprApp f' a'))
-- TODO: Da qui in poi controllare bene, non so se è giusto
typeExpr env (c, _, ExprLambda pat expr) = do
    argt <- typePat env pat
    env' <- patVarsInEnv (TyScheme []) env pat argt
    (s, t, e) <- typeExpr env' expr
    let finaldt = buildFunType (substApply s argt) t
        in return (s, finaldt, (c, finaldt, ExprLambda pat e))
typeExpr env (c, _, ExprPut val pses) = do
    (s, tval, val') <- typeExpr env val
    (s', tval') <- unifyPats (substApply s env) tval pses
    tempt <- freshType KType--TODO GIUSTO IL FRESH?
    (s'', texpr, pses') <- typePutBranches (substApply (composeSubst s' s) env) tval' tempt pses
    lift $ lift $ putStrLn $ show c ++ " PUT" ++ show tempt ++ " tval:" ++ show tval' ++ " texpr:"++show texpr
    return (composeSubst s'' (composeSubst s' s), texpr, (c, texpr, ExprPut val' pses'))

--Funzioni helper per putexpr
unifyPats :: TypingEnv -> DataType -> [(HLPattern, HLExpr)] -> TyperState (Subst, DataType)
unifyPats _ t [] = return (nullSubst, t)
unifyPats env t ((pat, (c, _, _)):branches) = do
    tpat <- typePat env pat
    s <- mgu c t tpat
    (s', t') <- unifyPats (substApply s env) (substApply s t) branches
    return (composeSubst s' s, t')

typePutBranches :: TypingEnv -> DataType -> DataType -> [(HLPattern, HLExpr)] -> TyperState (Subst, DataType, [(HLPattern, HLExpr)])
typePutBranches _ _ texpr [] = return (nullSubst, texpr, [])
typePutBranches env tpat texpr ((pat, expr@(c, _, _)):branches) = do
    lift $ lift $ putStrLn $ " PUTBRANCH_SRT tpat:" ++ show tpat ++ " texpr:" ++ show texpr
    env' <- patVarsInEnv (generalize env) env pat tpat
    (s, texpr', expr') <- typeExpr env' expr
    lift $ lift $ putStrLn $ " PUTBRANCH_TEX texpr: " ++ show texpr ++ " texpr':" ++ show texpr'
    s' <- mgu c texpr' texpr --TODO: è giusto l'ordine (texpr' prima)?
    mys <- return $ composeSubst s' s
    (s'', tfinal, others) <- typePutBranches (substApply mys env) (substApply mys tpat) (substApply s' texpr) branches
    lift $ lift $ putStrLn $ " PUTBRANCH_END tfinal:" ++ show tfinal ++ " s:" ++ show (composeSubst s'' mys)
    return (composeSubst s'' mys, tfinal, (pat, expr'):others)

--Sostituzioni su espressioni e definizioni, eseguite solo nel toplevel (riduci ancora il numero di applicazioni)
substApplyExpr :: Subst -> HLExpr -> HLExpr
substApplyExpr s (c, dt, ExprLiteral l) = (c, substApply s dt, ExprLiteral l)
substApplyExpr s (c, dt, ExprApp f a) = (c, substApply s dt, ExprApp (substApplyExpr s f) (substApplyExpr s a))
substApplyExpr s (c, dt, ExprLabel l) = (c, substApply s dt, ExprLabel l)
substApplyExpr s (c, dt, ExprConstructor l es) = (c, substApply s dt, ExprConstructor l (map (substApplyExpr s) es))
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
    t <- freshType KType
    env' <- return $ tyBindAdd c env s (TyScheme [] t)
    quantifiedValDefEnv env' vdefs

typeValDefsLoop _ [] = return (nullSubst, [])
typeValDefsLoop env (vdef:vdefs) = do
    (s, vdef') <- typeValDef env vdef
    (s', vdefs') <- typeValDefsLoop (substApply s env) vdefs
    return (composeSubst s' s, vdef':vdefs')

addValDefsEnv env vdefs = foldl
    (\e (ValDef c l (_, t, _))->
            tyBindAdd c e l (generalize e t)
        ) env vdefs

unionValDefEnv (TypingEnv ts _ _) (ValDef c l (_, t, _)) = do
    tFromEnv <- case Map.lookup l ts of
        Just scheme -> instantiate scheme
    s <- mgu c t tFromEnv
    lift $ lift $ putStrLn $ "union of env and vdef "++ l ++": " ++ show s
    return s

-- TODO: Quali di queste sostituzioni possono essere eliminate? (probabilmente quelle introdotte da typeValDefsLoop...)
-- TODO: Mi sa che questa funzione non dovrebbe restituire una sostituzione
typeValDefGroup env vdefs = do
    vars_env <- quantifiedValDefEnv env vdefs
    (s, vdefs') <- typeValDefsLoop vars_env vdefs
    substs <- mapM (unionValDefEnv (substApply s vars_env)) vdefs' -- Mi sa che questa cosa funziona solo perché le sostituzioni dovrebbero essere indipendenti l'una dall'altra a questo punto (cioè le due sostituzioni non contengono frecce discordanti e.g. q1->Int e q1->Flt) ... oppure è perché le sostituzioni vengono composte nel modo giusto???
    let s' = foldl (flip composeSubst) s substs
        vdefs'' = map (substApplyValDef s') vdefs'
        env' = addValDefsEnv (substApply s' env) vdefs''
        in if (0 == (length $ freetyvars env')) then return (s', env', vdefs'')
        else throwError $ show ((\(ValDef c _ _ )->c) $ head vdefs'') ++ " Ci sono delle variabili di tipo libere dopo la tipizzazione di un gruppo di valdef"

typeValDefGroups env [] = return (nullSubst, env, [])
typeValDefGroups env (vdefs:vdefss) = do
    (s, env', vdefs') <- typeValDefGroup env vdefs --TODO: forse anche questa sostituzione dopo averla applicata al contesto può essere eliminata
    (s', env'', vdefss') <- typeValDefGroups env' vdefss
    return (composeSubst s' s, env'', map (substApplyValDef s') vdefs':vdefss')
