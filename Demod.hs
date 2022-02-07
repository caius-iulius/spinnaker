module Demod (DemodEnv(..), demodModule, runDemodState, concatBlockPrograms) where
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as Map
import MPCL(StdCoord)
import TypingDefs (KindQuant, Kind(..), TyQuantId, TyQuant(..), Kind, DataType(DataNOTHING))
import HLDefs
import SyntaxDefs

data DemodEnv = DemodEnv 
    (Map.Map String (Visibility, DemodEnv)) -- Mods
    (Map.Map String (Visibility, String)) -- Vals
    (Map.Map String (Visibility, String)) -- Types
    (Map.Map String (Visibility, String)) -- Constructors
    deriving Show

envGetPubs (DemodEnv m v t c) = (DemodEnv (filterpub m) (filterpub v) (filterpub t) (filterpub c))
    where filterpub = Map.filter (\(v, _)->
            case v of
                Public -> True
                Private -> False
            )
envSetPrivate (DemodEnv m v t c) = (DemodEnv (setpriv m) (setpriv v) (setpriv t) (setpriv c))
    where setpriv = Map.map (\(_, e)->(Private, e))
--Al momento questo sceglie automaticamente l'elemento di sinistra quando c'è un'ambiguità. Bisogna considerare una scelta a destra o vincolare a contesti disgiunti
envsUnion :: DemodEnv -> DemodEnv -> DemodEnv
envsUnion (DemodEnv m v t c) (DemodEnv m' v' t' c') = DemodEnv (Map.union m m') (Map.union v v') (Map.union t t') (Map.union c c')

type DemodStateData = (Int, KindQuant, TyQuantId)
type DemodState t = ExceptT String (StateT DemodStateData IO) t

getPathEnv :: StdCoord -> DemodEnv -> [String] -> DemodState DemodEnv
getPathEnv _ env [] = return env
getPathEnv c (DemodEnv envs _ _ _) (entry:path) = case Map.lookup entry envs of
    Nothing -> throwError $ show c ++ " Could not find module: " ++ show entry
    Just (_, env) -> getPathEnv c env path

getUniqueSuffix :: DemodState String
getUniqueSuffix = do
    (u, k, t) <- get
    put (u+1, k, t)
    return ('#':show u)

freshKind :: DemodState Kind
freshKind = do
    (u, k, t) <- get
    put (u, k+1, t)
    return $ KindQuant k

newTyQuant :: Kind -> DemodState TyQuant
newTyQuant k = do
    (u, kq, tq) <- get
    put (u, kq, tq+1)
    return $ TyQuant tq k

-- Roba per i pattern
patsValsInEnv env [] = return (env, [])
patsValsInEnv env (p:ps) = do
    (env', p') <- patValsInEnv env p
    (env'', ps') <- patsValsInEnv env' ps
    return (env'', p':ps')

patValsInEnvInner _ env SynPatWildcard = return (env, PatWildcard)
patValsInEnvInner _ env (SynPatLiteral l) = return (env, PatLiteral l)
patValsInEnvInner _ env (SynPatTuple ps) = do
    (env', ps') <- patsValsInEnv env ps
    return (env', PatVariant ("()"++ (show $ length ps')) ps')
patValsInEnvInner c env (SynPatVariant pathlabl@(Path path labl) ps) = do
    (DemodEnv _ _ _ cs) <- getPathEnv c env path
    case Map.lookup labl cs of
        Nothing -> throwError $ show c ++ " Unbound constructor: " ++ show pathlabl
        Just (_, nlabl) -> do
            (env', ps') <- patsValsInEnv env ps
            return (env', PatVariant nlabl ps')

patValsInEnv :: DemodEnv -> SyntaxPattern -> DemodState (DemodEnv, HLPattern)
patValsInEnv env (c, Nothing, inner) = do
    (env', inner') <- patValsInEnvInner c env inner
    return (env', (c, Nothing, inner'))
patValsInEnv (DemodEnv ms vs ts cs) (c, Just l, inner) =
    case Map.lookup l vs of
        Just _ -> throwError $ show c ++ " Label: " ++ show l ++ " is already bound"
        Nothing -> do
            suffix <- getUniqueSuffix
            (env', inner') <- patValsInEnvInner c (DemodEnv ms (Map.union vs (Map.singleton l (Private, l++suffix))) ts cs) inner
            return (env', (c, Just $ l++suffix, inner'))

--espressioni
demodExpr _ (c, SynExprLiteral l) = return (c, DataNOTHING, ExprLiteral l)
demodExpr env (c, SynExprApp f a) = do
    f' <- demodExpr env f
    a' <- demodExpr env a
    return (c, DataNOTHING, ExprApp f' a')
demodExpr env (c, SynExprLabel pathlabl@(Path path labl)) = do
    (DemodEnv _ vs _ _) <- getPathEnv c env path
    case Map.lookup labl vs of
        Nothing -> throwError $ show c ++ " Unbound value: " ++ show pathlabl
        Just (_, nlabl) -> return (c, DataNOTHING, ExprLabel nlabl)
demodExpr env (c, SynExprConstructor pathlabl@(Path path labl)) = do
    (DemodEnv _ _ _ cs) <- getPathEnv c env path
    case Map.lookup labl cs of
        Nothing -> throwError $ show c ++ " Unbound constructor: " ++ show pathlabl
        Just (_, nlabl) -> return (c, DataNOTHING, ExprConstructor nlabl [])
demodExpr env (c, SynExprTuple es) =
    let buildExprTuple exprs = foldl (\tup ne -> (c, DataNOTHING, ExprApp tup ne)) (c, DataNOTHING, ExprConstructor ("()" ++ (show $ length exprs)) []) exprs
    in do
        es' <- mapM (demodExpr env) es
        return $ buildExprTuple es'
demodExpr env (c, SynExprLambda pat expr) = do
    (env', pat') <- patValsInEnv env pat
    expr' <- demodExpr env' expr
    return (c, DataNOTHING, ExprLambda pat' expr')
demodExpr env (c, SynExprPut val pses) = do
    val' <- demodExpr env val
    pses' <- mapM (\(pat, e)->do
        (env', pat') <- patValsInEnv env pat
        e' <- demodExpr env' e
        return (pat', e')
        ) pses
    return (c, DataNOTHING, ExprPut val' pses')

-- definizioni dei valori globali
demodValDef env (SynValDef c _ l e) = do
    e' <- demodExpr env e
    return (ValDef c l e')

valDefGroupEnv :: DemodEnv -> [SyntaxValDef] -> DemodState (DemodEnv, [SyntaxValDef])
valDefGroupEnv env [] = return (env, [])
valDefGroupEnv env@(DemodEnv _ vs _ _) (SynValDef c v l e:vvdefs) =
    case Map.lookup l vs of
        Just _ -> throwError $ show c ++ " Value: " ++ show l ++ " already bound"
        Nothing -> do
            suffix <- getUniqueSuffix
            (env', vdefs') <- valDefGroupEnv (envsUnion env (DemodEnv Map.empty (Map.singleton l (v, l++suffix)) Map.empty Map.empty)) vvdefs
            return (env', SynValDef c v (l++suffix) e:vdefs')

-- definizioni dei datatype
demodTypeExpr :: DemodEnv -> Map.Map String TyQuant -> SyntaxTypeExpr -> DemodState DataType
demodTypeExpr = error "TODO"

demodDataVar :: DemodEnv -> Map.Map String TyQuant -> SyntaxDataVariant -> DemodState HLDataVariant
demodDataVar env qmap (SynDataVariant c l tes) = do
    ts <- mapM (demodTypeExpr env qmap) tes
    return $ DataVariant c l ts

demodDataDef :: DemodEnv -> SyntaxDataDef -> DemodState HLDataDef
demodDataDef env (SynDataDef c _ l qls vars) = do
    qmap <- foldl (\mqmap ql -> do
        qmap <- mqmap
        newk <- freshKind
        newq <- newTyQuant newk
        case Map.lookup ql qmap of
            Just _ -> throwError $ show c ++ " Type quantifier: " ++ show ql ++ " already bound"
            Nothing -> return $ Map.union qmap (Map.singleton ql newq)
        ) (return Map.empty) qls
    vars' <- mapM (demodDataVar env qmap) vars
    return (DataDef c l (map snd $ Map.toList qmap) vars')

dataVarsEnv :: Visibility -> DemodEnv -> [SyntaxDataVariant] -> DemodState (DemodEnv, [SyntaxDataVariant])
dataVarsEnv _ env [] = return (env, [])
dataVarsEnv v env@(DemodEnv _ _ _ cs) (SynDataVariant c l tes:vardefs) =
    case Map.lookup l cs of
        Just _ -> throwError $ show c ++ " Constructor: " ++ show l ++ " already bound"
        Nothing -> do
            suffix <- getUniqueSuffix
            (env', vardefs') <- dataVarsEnv v (envsUnion env (DemodEnv Map.empty Map.empty Map.empty (Map.singleton l (v, l++suffix)))) vardefs
            return (env', SynDataVariant c (l++suffix) tes:vardefs')

dataDefGroupEnv :: DemodEnv -> [SyntaxDataDef] -> DemodState (DemodEnv, [SyntaxDataDef])
dataDefGroupEnv env [] = return (env, [])
dataDefGroupEnv env@(DemodEnv _ _ ts _) (SynDataDef c v l qs vars:ddefs) =
    case Map.lookup l ts of
        Just _ -> throwError $ show c ++ " Data: " ++ show l ++ " already bound"
        Nothing -> do
            suffix <- getUniqueSuffix
            (env', vars') <- dataVarsEnv v env vars
            (env'', ddefs') <- dataDefGroupEnv (envsUnion env' (DemodEnv Map.empty Map.empty (Map.singleton l (v, l++suffix)) Map.empty)) ddefs
            return (env'', SynDataDef c v (l++suffix) qs vars':ddefs')

-- moduli
demodModDef :: DemodEnv -> SyntaxModDef -> DemodState (DemodEnv, BlockProgram)
demodModDef env@(DemodEnv ms vs ts cs) (ModMod c v l m) =
    case Map.lookup l ms of
        Just _ -> throwError $ show c ++ " Module: " ++ show l ++ " already defined"
        Nothing -> do
            (menv, demodded) <- demodModule (envSetPrivate env) m
            lift $ lift $ putStrLn $ "Final module env of " ++ show l ++ ": " ++ show (envGetPubs menv)
            return (DemodEnv (Map.union ms (Map.singleton l (v, envGetPubs menv))) vs ts cs, demodded)
demodModDef env (ModUse c v (Path p l)) =
    let setVisib = case v of
            Public -> id
            Private -> envSetPrivate
    in do
        useEnv <- getPathEnv c env (p++[l])
        return $ (envsUnion (setVisib useEnv) env, BlockProgram [] [])
demodModDef env (ModValGroup vvdefs) = do
    (env', vdefs) <- valDefGroupEnv env vvdefs
    vdefs' <- mapM (demodValDef env') vdefs
    return (env', BlockProgram [] [vdefs'])
demodModDef env (ModDataGroup ddefs) = do
    (env', ddefs') <- dataDefGroupEnv env ddefs
    ddefs'' <- mapM (demodDataDef env') ddefs'
    return (env', BlockProgram [ddefs''] [])

concatBlockPrograms (BlockProgram datagroups valgroups) (BlockProgram datagroups' valgroups') = BlockProgram (datagroups++datagroups') (valgroups++valgroups')

demodModDefs env [] = return (env, BlockProgram [] [])
demodModDefs env (def:defs) = do
    (env', block) <- demodModDef env def
    (env'', block') <- demodModDefs env' defs
    return (env'', concatBlockPrograms block block')

demodModule :: DemodEnv -> SyntaxModule -> DemodState (DemodEnv, BlockProgram)
demodModule env (Module defs) = demodModDefs env defs

runDemodState :: DemodState t -> IO (Either String t)
runDemodState t = do
    (either, state) <- runStateT (runExceptT t) (0,0,0) --TODO: kindquant e tyquant serviranno al typer, vanno restituiti
    return either
