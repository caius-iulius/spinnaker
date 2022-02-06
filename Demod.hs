module Demod (DemodEnv(..), demodModule, runDemodState, concatBlockPrograms) where
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as Map
import MPCL(StdCoord)
import TypingDefs (DataType(DataNOTHING))
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

type DemodState t = ExceptT String (StateT Int IO) t

getPathEnv :: StdCoord -> DemodEnv -> [String] -> DemodState DemodEnv
getPathEnv _ env [] = return env
getPathEnv c (DemodEnv envs _ _ _) (entry:path) = case Map.lookup entry envs of
    Nothing -> throwError $ show c ++ " Could not find module: " ++ show entry
    Just (_, env) -> getPathEnv c env path

getUniqueSuffix :: DemodState String
getUniqueSuffix = do
    u <- get
    put (u+1)
    return ('#':show u)

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

demodValDef env (SynValDef c _ l e) = do
    e' <- demodExpr env e
    return (ValDef c l e')

valDefGroupEnv :: DemodEnv -> [SyntaxValDef] -> DemodState (DemodEnv, [SyntaxValDef])
valDefGroupEnv env [] = return (env, [])
valDefGroupEnv env@(DemodEnv ms vs ts cs) (SynValDef c v l e:vvdefs) =
    case Map.lookup l vs of
        Just _ -> throwError $ show c ++ " Value: " ++ show l ++ " already bound"
        Nothing -> do
            suffix <- getUniqueSuffix
            (env', vdefs') <- valDefGroupEnv (DemodEnv ms (Map.union (Map.singleton l (v, l++suffix)) vs) ts cs) vvdefs
            return (env', SynValDef c v (l++suffix) e:vdefs')

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
        return $ (envsUnion (setVisib useEnv) env, BlockProgram [])
demodModDef env (ModValGroup vvdefs) = do
    (env', vdefs) <- valDefGroupEnv env vvdefs
    vdefs' <- mapM (demodValDef env') vdefs
    return (env', BlockProgram [vdefs'])

concatBlockPrograms (BlockProgram valgroups) (BlockProgram valgroups') = BlockProgram $ valgroups++valgroups'

demodModDefs env [] = return (env, BlockProgram [])
demodModDefs env (def:defs) = do
    (env', block) <- demodModDef env def
    (env'', block') <- demodModDefs env' defs
    return (env'', concatBlockPrograms block block')

demodModule :: DemodEnv -> SyntaxModule -> DemodState (DemodEnv, BlockProgram)
demodModule env (Module defs) = demodModDefs env defs

runDemodState :: DemodState t -> IO (Either String t)
runDemodState t = do
    (either, state) <- runStateT (runExceptT t) 0
    return either
