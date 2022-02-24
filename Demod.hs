module Demod (DemodEnv(..), demodProgram) where
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as Map
import MPCL(StdCoord)
import TypingDefs
-- (KindQuant, Kind(..), TyQuantId, TyQuant(..), Kind, DataType(DataNOTHING))
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
envsUnionLeft :: DemodEnv -> DemodEnv -> DemodEnv
envsUnionLeft (DemodEnv m v t c) (DemodEnv m' v' t' c') = DemodEnv (Map.union m m') (Map.union v v') (Map.union t t') (Map.union c c')

getPathEnv :: StdCoord -> DemodEnv -> [String] -> TyperState DemodEnv
getPathEnv _ env [] = return env
getPathEnv c (DemodEnv envs _ _ _) (entry:path) = case Map.lookup entry envs of
    Nothing -> throwError $ show c ++ " Could not find module: " ++ show entry
    Just (_, env) -> getPathEnv c env path

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
patValsInEnvInner c env SynPatListNil = do
    (DemodEnv _ _ _ cs) <- getPathEnv c env ["Core"]
    case Map.lookup "Nil" cs of
        Nothing -> throwError $ show c ++ " The Core module does not provide a definition for Nil"
        Just (_, nlabl) -> return (env, PatVariant nlabl [])
patValsInEnvInner c env (SynPatListConss ps final) = do
    (DemodEnv _ _ _ cs) <- getPathEnv c env ["Core"]
    case Map.lookup "Cons" cs of
        Nothing -> throwError $ show c ++ " The Core module does not provide a definition for Cons"
        Just (_, nlabl) -> do
            (env', ps') <- patsValsInEnv env ps
            (env'', final') <- patValsInEnv env' final
            return $ (\(_,_,r)->(env'', r)) $ foldr (\head tail -> (c, Nothing, PatVariant nlabl [head, tail])) final' ps'

patValsInEnv :: DemodEnv -> SyntaxPattern -> TyperState (DemodEnv, HLPattern)
patValsInEnv env (c, Nothing, inner) = do
    (env', inner') <- patValsInEnvInner c env inner
    return (env', (c, Nothing, inner'))
patValsInEnv (DemodEnv ms vs ts cs) (c, Just l, inner) =
    case Map.lookup l vs of
        Just _ -> throwError $ show c ++ " Label: " ++ show l ++ " is already bound"
        Nothing -> do
            suffix <- newUniqueSuffix
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
demodExpr env (c, SynExprTuple es) = do
        es' <- mapM (demodExpr env) es
        return (c, DataNOTHING, ExprConstructor ("()"++(show $ length es')) es')
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
demodExpr env (c, SynExprListNil) = do --TODO: Forse questo si può ridurre a un demodExpr di un SynExprConstructor
    (DemodEnv _ _ _ cs) <- getPathEnv c env ["Core"]
    case Map.lookup "Nil" cs of
        Nothing -> throwError $ show c ++ " The Core module does not provide a definition for Nil"
        Just (_, nlabl) -> return (c, DataNOTHING, ExprConstructor nlabl [])
demodExpr env (c, SynExprListConss es final) = do
    (DemodEnv _ _ _ cs) <- getPathEnv c env ["Core"]
    case Map.lookup "Cons" cs of
        Nothing -> throwError $ show c ++ " The Core module does not provide a definition for Cons"
        Just (_, nlabl) -> do
            demodes <- mapM (demodExpr env) es
            demodfinal <- demodExpr env final
            return $ foldr (\head tail -> (c, DataNOTHING, ExprConstructor nlabl [head, tail])) demodfinal demodes
demodExpr env (c, SynExprIfThenElse cond iftrue iffalse) = demodExpr env (c, --TODO: Forse questo va "specializzato" come le implementazioni di synexprlistnil etc...
    SynExprPut cond [
        ((c, Nothing, SynPatVariant (Path ["Core"] "True") []), iftrue),
        ((c, Nothing, SynPatVariant (Path ["Core"] "False") []), iffalse)
    ])
demodExpr env (c, SynExprInlineUse (Path path labl) e) = do
    env' <- getPathEnv c env (path ++ [labl])
    demodExpr (envsUnionLeft env' env) e

-- definizioni dei valori globali
demodTySchemeExpr :: DemodEnv -> SyntaxTySchemeExpr -> TyperState HLTySchemeExpr
demodTySchemeExpr env (c, qls, te) = do --TODO: Questo codice fa cagare ed è duplicato
    (qmap, _) <- buildQmapQlist c qls
    demodTypeExpr env qmap te

demodValDef env (SynValDef c _ l t e) = do
    t' <- case t of
        Nothing -> return $ Nothing
        Just te -> do
            te' <- demodTySchemeExpr env te
            return $ Just (te', DataNOTHING)
    e' <- demodExpr env e
    return (ValDef c l t' e')

valDefGroupEnv :: DemodEnv -> [SyntaxValDef] -> TyperState (DemodEnv, [SyntaxValDef])
valDefGroupEnv env [] = return (env, [])
valDefGroupEnv env@(DemodEnv _ vs _ _) (SynValDef c v l t e:vvdefs) =
    case Map.lookup l vs of
        Just _ -> throwError $ show c ++ " Value: " ++ show l ++ " already bound"
        Nothing -> do
            suffix <- newUniqueSuffix
            (env', vdefs') <- valDefGroupEnv (envsUnionLeft env (DemodEnv Map.empty (Map.singleton l (v, l++suffix)) Map.empty Map.empty)) vvdefs
            return (env', SynValDef c v (l++suffix) t e:vdefs')

-- definizioni dei datatype
demodTypeExpr :: DemodEnv -> Map.Map String TyQuant -> SyntaxTypeExpr -> TyperState HLTypeExpr
demodTypeExpr env qmap (c, SynTypeExprQuantifier l) =
    case Map.lookup l qmap of
        Nothing -> throwError $ show c ++ " Type quantifier: " ++ show l ++ " not bound"
        Just q -> return (c, TypeExprQuant q)
demodTypeExpr env qmap (c, SynTypeExprTuple stes) = do
    tes <- mapM (demodTypeExpr env qmap) stes
    return $ foldl (\tef tea -> (c, TypeExprApp tef tea)) (c, TypeExprName $ "()" ++ (show $ length tes)) tes
demodTypeExpr env qmap (c, SynTypeExprName pathlabl@(Path path labl)) = do
    (DemodEnv _ _ ts _) <- getPathEnv c env path
    case Map.lookup labl ts of
        Nothing -> throwError $ show c ++ " Type label: " ++ show pathlabl ++ " not bound"
        Just (_, nlabl) -> return (c, TypeExprName nlabl)
demodTypeExpr env qmap (c, SynTypeExprApp stef steas) = do
    tef <- demodTypeExpr env qmap stef
    teas <- mapM (demodTypeExpr env qmap) steas
    return $ foldl (\f a -> (c, TypeExprApp f a)) tef teas --TODO: Le applicazioni di typesyn vanno gestite diversamente

buildQmapQlist c qls =
    foldl (\mqmapqlist ql -> do
        (qmap, qlist) <- mqmapqlist
        newk <- freshKind
        newq <- newTyQuant newk
        case Map.lookup ql qmap of
            Just _ -> throwError $ show c ++ " Type quantifier: " ++ show ql ++ " already bound"
            Nothing -> return $ (Map.union qmap (Map.singleton ql newq), qlist ++ [(ql, newq)])
        ) (return (Map.empty, [])) qls

demodDataVar :: DemodEnv -> Map.Map String TyQuant -> SyntaxDataVariant -> TyperState HLDataVariant
demodDataVar env qmap (SynDataVariant c l stes) = do
    tes <- mapM (demodTypeExpr env qmap) stes
    return $ DataVariant c l (map (\te->(te,DataNOTHING)) tes)

demodDataDef :: DemodEnv -> SyntaxDataDef -> TyperState HLDataDef
demodDataDef env (SynDataDef c _ l qls vars) = do --TODO: Questo codice fa cagare
    (qmap, qlist) <- buildQmapQlist c qls
    vars' <- mapM (demodDataVar env qmap) vars
    return (DataDef c l qlist vars')

dataVarsEnv :: Visibility -> DemodEnv -> [SyntaxDataVariant] -> TyperState (DemodEnv, [SyntaxDataVariant])
dataVarsEnv _ env [] = return (env, [])
dataVarsEnv v env@(DemodEnv _ _ _ cs) (SynDataVariant c l tes:vardefs) =
    case Map.lookup l cs of
        Just _ -> throwError $ show c ++ " Constructor: " ++ show l ++ " already bound"
        Nothing -> do
            suffix <- newUniqueSuffix
            (env', vardefs') <- dataVarsEnv v (envsUnionLeft env (DemodEnv Map.empty Map.empty Map.empty (Map.singleton l (v, l++suffix)))) vardefs
            return (env', SynDataVariant c (l++suffix) tes:vardefs')

dataDefGroupEnv :: DemodEnv -> [SyntaxDataDef] -> TyperState (DemodEnv, [SyntaxDataDef])
dataDefGroupEnv env [] = return (env, [])
dataDefGroupEnv env@(DemodEnv _ _ ts _) (SynDataDef c v l qs vars:ddefs) =
    case Map.lookup l ts of
        Just _ -> throwError $ show c ++ " Data: " ++ show l ++ " already bound"
        Nothing -> do
            suffix <- newUniqueSuffix
            (env', vars') <- dataVarsEnv v env vars
            (env'', ddefs') <- dataDefGroupEnv (envsUnionLeft env' (DemodEnv Map.empty Map.empty (Map.singleton l (v, l++suffix)) Map.empty)) ddefs
            return (env'', SynDataDef c v (l++suffix) qs vars':ddefs')

-- moduli
demodModDef :: DemodEnv -> SyntaxModDef -> TyperState (DemodEnv, BlockProgram)
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
        return $ (envsUnionLeft (setVisib useEnv) env, BlockProgram [] [])
demodModDef env (ModValGroup vvdefs) = do
    (env', vdefs) <- valDefGroupEnv env vvdefs
    vdefs' <- mapM (demodValDef env') vdefs
    return (env', BlockProgram [] [vdefs'])
demodModDef env (ModDataGroup ddefs) = do
    (env', ddefs') <- dataDefGroupEnv env ddefs
    ddefs'' <- mapM (demodDataDef env') ddefs'
    return (env', BlockProgram [ddefs''] [])
demodModDef env (ModTypeSyn _ _ _ _ _) = error "TODO demod dei typesyn. Vanno sostituiti qui o restano nel HLDefs?"

concatBlockPrograms (BlockProgram datagroups valgroups) (BlockProgram datagroups' valgroups') = BlockProgram (datagroups++datagroups') (valgroups++valgroups')

demodModDefs env [] = return (env, BlockProgram [] [])
demodModDefs env (def:defs) = do
    (env', block) <- demodModDef env def
    (env'', block') <- demodModDefs env' defs
    return (env'', concatBlockPrograms block block')

demodModule :: DemodEnv -> SyntaxModule -> TyperState (DemodEnv, BlockProgram)
demodModule env (Module defs) = demodModDefs env defs

demodProgram :: DemodEnv -> SyntaxModule -> SyntaxModule -> TyperState (DemodEnv, BlockProgram)
demodProgram initCoreDemodEnv core mod = do
    (coreEnv, coreBlock) <- demodModule initCoreDemodEnv core
    lift $ lift $ putStrLn $ "coreEnv: " ++ show coreEnv
    (modEnv, modBlock) <- demodModule (DemodEnv (Map.singleton "Core" (Private, envGetPubs coreEnv)) Map.empty Map.empty Map.empty) mod
    lift $ lift $ putStrLn $ "Final demodEnv: " ++ show modEnv
    --lift $ lift $ putStrLn $ "Demodded Core: " ++ (drawTree $ toTreeBlockProgram coreBlock)
    --lift $ lift $ putStrLn $ "Demodded: " ++ (drawTree $ toTreeBlockProgram modBlock)
    return (modEnv, concatBlockPrograms coreBlock modBlock)
