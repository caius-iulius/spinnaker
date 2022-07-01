module Demod (DemodEnv(..), concatBlockPrograms, demodExpr, demodProgram) where
import Control.Monad.Trans
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
    (Map.Map String (Visibility, (String, Map.Map String String))) -- Rels
    deriving Show

envGetPubs (DemodEnv m v t c r) = (DemodEnv (filterpub m) (filterpub v) (filterpub t) (filterpub c) (filterpub r))
    where filterpub = Map.filter (\(v, _)->
            case v of
                Public -> True
                Private -> False
            )
envSetPrivate (DemodEnv m v t c r) = (DemodEnv (setpriv m) (setpriv v) (setpriv t) (setpriv c) (setpriv r))
    where setpriv = Map.map (\(_, e)->(Private, e))
--Al momento questo sceglie automaticamente l'elemento di sinistra quando c'è un'ambiguità. Bisogna considerare una scelta a destra o vincolare a contesti disgiunti
envsUnionLeft :: DemodEnv -> DemodEnv -> DemodEnv
envsUnionLeft (DemodEnv m v t c r) (DemodEnv m' v' t' c' r') = DemodEnv (Map.union m m') (Map.union v v') (Map.union t t') (Map.union c c') (Map.union r r')

getPathEnv :: StdCoord -> DemodEnv -> [String] -> TyperState DemodEnv
getPathEnv _ env [] = return env
getPathEnv c (DemodEnv envs _ _ _ _) (entry:path) = case Map.lookup entry envs of
    Nothing -> fail $ show c ++ " Could not find module: " ++ show entry
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
    (DemodEnv _ _ _ cs _) <- getPathEnv c env path
    case Map.lookup labl cs of
        Nothing -> fail $ show c ++ " Unbound constructor: " ++ show pathlabl
        Just (_, nlabl) -> do
            (env', ps') <- patsValsInEnv env ps
            return (env', PatVariant nlabl ps')
patValsInEnvInner c env SynPatListNil = do
    (DemodEnv _ _ _ cs _) <- getPathEnv c env ["Core"]
    case Map.lookup "Nil" cs of
        Nothing -> fail $ show c ++ " The Core module does not provide a definition for Nil"
        Just (_, nlabl) -> return (env, PatVariant nlabl [])
patValsInEnvInner c env (SynPatListConss ps final) = do
    (DemodEnv _ _ _ cs _) <- getPathEnv c env ["Core"]
    case Map.lookup "Cons" cs of
        Nothing -> fail $ show c ++ " The Core module does not provide a definition for Cons"
        Just (_, nlabl) -> do
            (env', ps') <- patsValsInEnv env ps
            (env'', final') <- patValsInEnv env' final
            return $ (\(_,_,r)->(env'', r)) $ foldr (\head tail -> (c, Nothing, PatVariant nlabl [head, tail])) final' ps'

patValsInEnv :: DemodEnv -> SyntaxPattern -> TyperState (DemodEnv, HLPattern)
patValsInEnv env (c, Nothing, inner) = do
    (env', inner') <- patValsInEnvInner c env inner
    return (env', (c, Nothing, inner'))
patValsInEnv (DemodEnv ms vs ts cs rs) (c, Just l, inner)
    | Map.member l vs = fail $ show c ++ " Label: " ++ show l ++ " is already bound"
    | otherwise = do
        suffix <- newUniqueSuffix
        (env', inner') <- patValsInEnvInner c (DemodEnv ms (Map.insert l (Private, l++suffix) vs) ts cs rs) inner
        return (env', (c, Just $ l++suffix, inner'))

--espressioni
demodExpr _ (c, SynExprLiteral l) = return (c, DataNOTHING, ExprLiteral l)
demodExpr env (c, SynExprApp f a) = do
    f' <- demodExpr env f
    a' <- demodExpr env a
    return (c, DataNOTHING, ExprApp f' a')
demodExpr env (c, SynExprLabel pathlabl@(Path path labl)) = do
    (DemodEnv _ vs _ _ _) <- getPathEnv c env path
    case Map.lookup labl vs of
        Nothing -> fail $ show c ++ " Unbound value: " ++ show pathlabl
        Just (_, nlabl) -> return (c, DataNOTHING, ExprLabel nlabl)
demodExpr env (c, SynExprConstructor pathlabl@(Path path labl)) = do
    (DemodEnv _ _ _ cs _) <- getPathEnv c env path
    case Map.lookup labl cs of
        Nothing -> fail $ show c ++ " Unbound constructor: " ++ show pathlabl
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
    (DemodEnv _ _ _ cs _) <- getPathEnv c env ["Core"]
    case Map.lookup "Nil" cs of
        Nothing -> fail $ show c ++ " The Core module does not provide a definition for Nil"
        Just (_, nlabl) -> return (c, DataNOTHING, ExprConstructor nlabl [])
demodExpr env (c, SynExprListConss es final) = do
    (DemodEnv _ _ _ cs _) <- getPathEnv c env ["Core"]
    case Map.lookup "Cons" cs of
        Nothing -> fail $ show c ++ " The Core module does not provide a definition for Cons"
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
demodTySchemeExpr :: DemodEnv -> Map.Map String TyQuant -> SyntaxTySchemeExpr -> TyperState (Qual DataType)
demodTySchemeExpr env qmap (c, qls, ps, te) = do
    (qmap', _) <- buildQmapQlist c qls
    if (length $ Map.intersection qmap qmap') /= 0
        then fail $ show c ++ " Type scheme declares already used tyquants (TODO: migliora l'error reporting)"
        else do
            ps' <- mapM (demodPred env (Map.union qmap' qmap)) ps
            te' <- demodTypeExpr env (Map.union qmap' qmap) te
            return $ Qual ps' te'

demodValDef env (SynValDef c _ l t e) = do
    t' <- case t of
        Nothing -> return $ Nothing
        Just te -> do
            te' <- demodTySchemeExpr env Map.empty te
            return $ Just te'
    e' <- demodExpr env e
    return (ValDef c l t' [] e')

valDefGroupEnv :: DemodEnv -> [SyntaxValDef] -> TyperState (DemodEnv, [SyntaxValDef])
valDefGroupEnv env [] = return (env, [])
valDefGroupEnv env@(DemodEnv _ vs _ _ _) (SynValDef c v l t e:vvdefs)
    | Map.member l vs = fail $ show c ++ " Value: " ++ show l ++ " already bound"
    | otherwise = do
        suffix <- newUniqueSuffix
        (env', vdefs') <- valDefGroupEnv (envsUnionLeft env (DemodEnv Map.empty (Map.singleton l (v, l++suffix)) Map.empty Map.empty Map.empty)) vvdefs
        return (env', SynValDef c v (l++suffix) t e:vdefs')

-- definizioni dei datatype
demodTypeExpr :: DemodEnv -> Map.Map String TyQuant -> SyntaxTypeExpr -> TyperState DataType
demodTypeExpr env qmap (c, SynTypeExprQuantifier l) =
    case Map.lookup l qmap of
        Nothing -> fail $ show c ++ " Type quantifier: " ++ show l ++ " not bound"
        Just q -> return $ DataCOORD c (DataQuant q)
demodTypeExpr env qmap (c, SynTypeExprTuple stes) = do
    tes <- mapM (demodTypeExpr env qmap) stes
    return $ foldl (\tef tea -> DataCOORD c (DataTypeApp tef tea)) (DataCOORD c (DataTypeName ("()" ++ (show $ length tes)) KindNOTHING)) tes
demodTypeExpr env qmap (c, SynTypeExprName pathlabl@(Path path labl)) = do
    (DemodEnv _ _ ts _ _) <- getPathEnv c env path
    case Map.lookup labl ts of
        Nothing -> fail $ show c ++ " Type label: " ++ show pathlabl ++ " not bound"
        Just (_, nlabl) -> return $ DataCOORD c (DataTypeName nlabl KindNOTHING)
demodTypeExpr env qmap (c, SynTypeExprApp stef steas) = do
    tef <- demodTypeExpr env qmap stef
    teas <- mapM (demodTypeExpr env qmap) steas
    return $ foldl (\f a -> DataCOORD c (DataTypeApp f a)) tef teas --TODO: Le applicazioni di typesyn vanno gestite diversamente

buildQmapQlist c qls =
    foldl (\mqmapqlist ql -> do
        (qmap, qlist) <- mqmapqlist
        newk <- freshKind
        newq <- newTyQuant newk
        if Map.member ql qmap
            then fail $ show c ++ " Type quantifier: " ++ show ql ++ " already bound"
            else return $ (Map.insert ql newq qmap, qlist ++ [(ql, newq)])
        ) (return (Map.empty, [])) qls

demodDataVar :: DemodEnv -> Map.Map String TyQuant -> SyntaxDataVariant -> TyperState HLDataVariant
demodDataVar env qmap (SynDataVariant c l stes) = do
    tes <- mapM (demodTypeExpr env qmap) stes
    return $ DataVariant c l (map (\(DataCOORD c t)->(c, DataCOORD c t)) tes)

demodDataDef :: DemodEnv -> SyntaxDataDef -> TyperState HLDataDef
demodDataDef env (SynDataDef c _ l qls vars) = do --TODO: Questo codice fa cagare
    (qmap, qlist) <- buildQmapQlist c qls
    vars' <- mapM (demodDataVar env qmap) vars
    return (DataDef c l qlist vars')

dataVarsEnv :: Visibility -> DemodEnv -> [SyntaxDataVariant] -> TyperState (DemodEnv, [SyntaxDataVariant])
dataVarsEnv _ env [] = return (env, [])
dataVarsEnv v env@(DemodEnv _ _ _ cs _) (SynDataVariant c l tes:vardefs)
    | Map.member l cs = fail $ show c ++ " Constructor: " ++ show l ++ " already bound"
    | otherwise = do
        suffix <- newUniqueSuffix
        (env', vardefs') <- dataVarsEnv v (envsUnionLeft env (DemodEnv Map.empty Map.empty Map.empty (Map.singleton l (v, l++suffix)) Map.empty)) vardefs
        return (env', SynDataVariant c (l++suffix) tes:vardefs')

dataDefGroupEnv :: DemodEnv -> [SyntaxDataDef] -> TyperState (DemodEnv, [SyntaxDataDef])
dataDefGroupEnv env [] = return (env, [])
dataDefGroupEnv env@(DemodEnv _ _ ts _ _) (SynDataDef c v l qs vars:ddefs)
    | Map.member l ts = fail $ show c ++ " Data: " ++ show l ++ " already bound"
    | otherwise = do
        suffix <- newUniqueSuffix
        (env', vars') <- dataVarsEnv v env vars
        (env'', ddefs') <- dataDefGroupEnv (envsUnionLeft env' (DemodEnv Map.empty Map.empty (Map.singleton l (v, l++suffix)) Map.empty Map.empty)) ddefs
        return (env'', SynDataDef c v (l++suffix) qs vars':ddefs')

-- rel & inst
demodRelDecl env@(DemodEnv ms vs ts cs rs) qmap visib (c, l, tyscheme)
    | Map.member l vs = fail $ show c ++ " Value: " ++ show l ++ " already declared"
    | otherwise = do
        suffix <- newUniqueSuffix
        dt <- demodTySchemeExpr env qmap tyscheme
        return (DemodEnv ms (Map.insert l (visib, l++suffix) vs) ts cs rs, Map.singleton l (l++suffix), (c, l++suffix, dt))
demodRelDecls env qmap visib [] = return (env, Map.empty, [])
demodRelDecls env qmap visib (decl:decls) = do
    (env', relenv, decl') <- demodRelDecl env qmap visib decl
    (env'', relenv', decls') <- demodRelDecls env' qmap visib decls
    return (env'', Map.union relenv' relenv, decl':decls')

demodPred env qmap (c, pathlabl@(Path path labl), steas) = do
    (DemodEnv _ _ _ _ rs) <- getPathEnv c env path
    case Map.lookup labl rs of
        Nothing -> fail $ show c ++ " Rel label: " ++ show pathlabl ++ " not bound"
        Just (_, (nlabl, _)) -> do
            teas <- mapM (demodTypeExpr env qmap) steas
            return $ Pred nlabl teas

demodInstDefs rc rpath env relenv defs = loop [] relenv defs
    where loop final mrelenv []
            | length mrelenv == 0 = return $ reverse final
            | otherwise = fail $ show rc ++ " Instance for: " ++ show rpath ++ " should define: " ++ (show $ map fst $ Map.toList mrelenv)
          loop final mrelenv ((c, l, e):mdefs) =
            case Map.lookup l mrelenv of
                Nothing -> fail $ show c ++ " Member " ++ show l ++ " of instance for: " ++ show rpath ++ 
                    if any (\(_, l', _) -> l == l') final
                    then " has already been defined"
                    else " isn't declared and shouldn't be defined"
                Just newlabl -> do
                    e' <- demodExpr env e
                    loop ((c, newlabl, e'):final) (Map.delete l mrelenv) mdefs
-- moduli
demodModDef :: DemodEnv -> SyntaxModDef -> TyperState (DemodEnv, BlockProgram)
demodModDef env@(DemodEnv ms vs ts cs rs) (ModMod c v l m)
    | Map.member l ms = fail $ show c ++ " Module: " ++ show l ++ " already defined"
    | otherwise = do
        (menv, demodded) <- demodModule (envSetPrivate env) m
        lift $ lift $ putStrLn $ "Final module env of " ++ show l ++ ": " ++ show (envGetPubs menv)
        return (DemodEnv (Map.insert l (v, envGetPubs menv) ms) vs ts cs rs, demodded)
demodModDef env (ModUse c v (Path p l)) =
    let setVisib = case v of
            Public -> id
            Private -> envSetPrivate
    in do
        useEnv <- getPathEnv c env (p++[l])
        return $ (envsUnionLeft (setVisib useEnv) env, BlockProgram [] [] [] [])
demodModDef env (ModValGroup vvdefs) = do
    (env', vdefs) <- valDefGroupEnv env vvdefs
    vdefs' <- mapM (demodValDef env') vdefs
    return (env', BlockProgram [] [] [vdefs'] [])
demodModDef env (ModDataGroup ddefs) = do
    (env', ddefs') <- dataDefGroupEnv env ddefs
    ddefs'' <- mapM (demodDataDef env') ddefs'
    return (env', BlockProgram [ddefs''] [] [] [])
demodModDef env@(DemodEnv ms vs ts cs rs) (ModRel c visib l qls decls)
    | Map.member l rs = fail $ show c ++ " Rel: " ++ show l ++ " already defined"
    | otherwise = do
        suffix <- newUniqueSuffix
        (qmap, qlist) <- buildQmapQlist c qls
        (DemodEnv ms' vs' ts' cs' rs', relenv, decls') <- demodRelDecls env qmap visib decls
        return (DemodEnv ms' vs' ts' cs' (Map.insert l (visib, (l++suffix, relenv)) rs'), BlockProgram [] [RelDef c (l++suffix) (map snd qlist) decls'] [] [])
demodModDef env (ModInst c qls preds head@(_, rpl@(Path rpath rlabl), _) defs) = do
    (qmap, qlist) <- buildQmapQlist c qls
    preds' <- mapM (demodPred env qmap) preds
    pred' <- demodPred env qmap head
    (DemodEnv _ _ _ _ rs) <- getPathEnv c env rpath
    let relenv = case Map.lookup rlabl rs of
            Just (_, (_, relenv)) -> relenv
    defs' <- demodInstDefs c rpl env relenv defs
    return (env, BlockProgram [] [] [] [InstDef c (Qual preds' pred') defs'])
demodModDef env (ModTypeSyn _ _ _ _ _) = error "TODO demod dei typesyn. Vanno sostituiti qui o restano nel HLDefs?"

concatBlockPrograms (BlockProgram datagroups reldefs valgroups instdefs) (BlockProgram datagroups' reldefs' valgroups' instdefs') = BlockProgram (datagroups++datagroups') (reldefs++reldefs') (valgroups++valgroups') (instdefs++instdefs')

demodModDefs env [] = return (env, BlockProgram [] [] [] [])
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
    (modEnv, modBlock) <- demodModule (DemodEnv (Map.singleton "Core" (Private, envGetPubs coreEnv)) Map.empty Map.empty Map.empty Map.empty) mod
    lift $ lift $ putStrLn $ "Final demodEnv: " ++ show modEnv
    --lift $ lift $ putStrLn $ "Demodded Core: " ++ (drawTree $ toTreeBlockProgram coreBlock)
    --lift $ lift $ putStrLn $ "Demodded: " ++ (drawTree $ toTreeBlockProgram modBlock)
    return (modEnv, concatBlockPrograms coreBlock modBlock)
