module Demod (DemodEnv(..), concatBlockPrograms, demodExpr, demodProgram) where

import System.IO

import Control.Monad.Trans
import qualified Data.Map as Map
import MPCL(parse, ParseResult(..), StdCoord(Coord))
import Parser
import TypingDefs
import HLDefs
import SyntaxDefs

data EnvVisib = LocPub | LocPriv | ExtPub | ExtPriv
    deriving Show

visibtoenv Public = LocPub
visibtoenv Private = LocPriv
isLocal LocPub = True
isLocal LocPriv = True
isLocal _ = False

data DemodEnv = DemodEnv
    (Map.Map String (EnvVisib, DemodEnv)) -- Mods
    (Map.Map String (EnvVisib, String)) -- Vals
    (Map.Map String (EnvVisib, String)) -- Types
    (Map.Map String (EnvVisib, String)) -- Constructors
    (Map.Map String (EnvVisib, (String, Map.Map String String))) -- Rels
    deriving Show

--Definizioni builtin per Demod
builtinDemodTypes = ["->", "Int", "Flt", "Bool", "Chr", "RealWorld_"]
builtinDemodVars = ["True", "False", "RealWorld_"]

buildBIDemod l = (l, (LocPub, l++"#BI"))
buildBIDemodMap = Map.fromList . map buildBIDemod

initCoreDemodEnv = DemodEnv Map.empty Map.empty (buildBIDemodMap builtinDemodTypes) (buildBIDemodMap builtinDemodVars) Map.empty

entryPointBlock env = do
    hle <- demodExpr env Map.empty syne
    let entryPointVDef = ValDef c "entryPoint#BI" (Just (Qual [] realworldT)) [] hle
    return $ BlockProgram [] [] [] [[entryPointVDef]] []
    where c = Coord "entryPoint" 0 0
          syne = (c, SynExprApp (c, SynExprLabel (Path ["Core", "UnsafeIO"] "runTopIO"))
                    (c, SynExprApp (c, SynExprLabel (Path ["Core"] "runProgramTop")) (c, SynExprLabel (Path [] "main"))))

-- Demod vero e proprio

envGetPubs (DemodEnv m v t c r) = (DemodEnv (filterpub m) (filterpub v) (filterpub t) (filterpub c) (filterpub r))
    where filterpub = Map.filter (\(v, _)->
            case v of
                LocPub -> True
                ExtPub -> True
                _ -> False
            )
envGetExts (DemodEnv m v t c r) = envGetPubs (DemodEnv (filterpub m) (filterpub v) (filterpub t) (filterpub c) (filterpub r))
    where filterpub = fmap (\(v, e)->
            (case v of
                LocPub -> ExtPub
                LocPriv -> ExtPriv
                _ -> v, e)
            )
envSetPrivate (DemodEnv m v t c r) = (DemodEnv (setpriv m) (setpriv v) (setpriv t) (setpriv c) (setpriv r))
    where setpriv = Map.map (\(v, e)->
            (case v of
                LocPub -> LocPriv
                ExtPub -> ExtPriv
                _ -> v, e)
            )
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
    return (env', PatVariant (makeTupLabl $ length ps') ps')
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
        (env', inner') <- patValsInEnvInner c (DemodEnv ms (Map.insert l (visibtoenv Private, l++suffix) vs) ts cs rs) inner
        return (env', (c, Just $ l++suffix, inner'))

--espressioni
demodExpr _ _ (c, SynExprLiteral l) = return (c, DataNOTHING, ExprLiteral l)
demodExpr env qmap (c, SynExprApp f a) = do
    f' <- demodExpr env qmap f
    a' <- demodExpr env qmap a
    return (c, DataNOTHING, ExprApp f' a')
demodExpr env _ (c, SynExprLabel pathlabl@(Path path labl)) = do
    (DemodEnv _ vs _ _ _) <- getPathEnv c env path
    case Map.lookup labl vs of
        Nothing -> fail $ show c ++ " Unbound value: " ++ show pathlabl
        Just (_, nlabl) -> return (c, DataNOTHING, ExprLabel nlabl)
demodExpr env _ (c, SynExprConstructor pathlabl@(Path path labl)) = do
    (DemodEnv _ _ _ cs _) <- getPathEnv c env path
    case Map.lookup labl cs of
        Nothing -> fail $ show c ++ " Unbound constructor: " ++ show pathlabl
        Just (_, nlabl) -> return (c, DataNOTHING, ExprConstructor nlabl [])
demodExpr env qmap (c, SynExprTuple es) = do
        es' <- mapM (demodExpr env qmap) es
        return (c, DataNOTHING, ExprConstructor (makeTupLabl $ length es') es')
demodExpr env qmap (c, SynExprLambda pat expr) = do
    (env', pat') <- patValsInEnv env pat
    expr' <- demodExpr env' qmap expr
    return (c, DataNOTHING, ExprLambda pat' expr')
demodExpr env qmap (c, SynExprSndSection op expr) = do
    op' <- demodExpr env qmap (c, SynExprLabel op)
    expr' <- demodExpr env qmap expr
    suffix <- newUniqueSuffix
    let label = "_v" ++ suffix
    return (c, DataNOTHING, ExprLambda (c, Just label, PatWildcard) (c, DataNOTHING, ExprApp (c, DataNOTHING, ExprApp op' (c, DataNOTHING, ExprLabel label)) expr'))
demodExpr env qmap (c, SynExprPut val pses) = do
    val' <- demodExpr env qmap val
    pses' <- mapM (\(pat, e)->do
        (env', pat') <- patValsInEnv env pat
        e' <- demodExpr env' qmap e
        return (pat', e')
        ) pses
    return (c, DataNOTHING, ExprPut val' pses')
demodExpr env _ (c, SynExprString s) = do
    (DemodEnv _ vs _ cs _) <- getPathEnv c env ["Core"]
    case Map.lookup "Cons" cs of
        Nothing -> fail $ show c ++ " The Core module does not provide a definition for Cons"
        Just (_, conslabl) -> case Map.lookup "strNil" vs of
            Nothing -> fail $ show c ++ " The Core module does not provide a definition for strNil"
            Just (_, nillabl) -> return $
                foldr (\chr rest -> (c, DataNOTHING, ExprConstructor conslabl [(c, DataNOTHING, ExprLiteral (LitCharacter chr)), rest])) (c, DataNOTHING, ExprLabel nillabl) s
demodExpr env _ (c, SynExprListNil) = do --TODO: Forse questo si può ridurre a un demodExpr di un SynExprConstructor
    (DemodEnv _ _ _ cs _) <- getPathEnv c env ["Core"]
    case Map.lookup "Nil" cs of
        Nothing -> fail $ show c ++ " The Core module does not provide a definition for Nil"
        Just (_, nlabl) -> return (c, DataNOTHING, ExprConstructor nlabl [])
demodExpr env qmap (c, SynExprListConss es final) = do
    (DemodEnv _ _ _ cs _) <- getPathEnv c env ["Core"]
    case Map.lookup "Cons" cs of
        Nothing -> fail $ show c ++ " The Core module does not provide a definition for Cons"
        Just (_, nlabl) -> do
            demodes <- mapM (demodExpr env qmap) es
            demodfinal <- demodExpr env qmap final
            return $ foldr (\head tail -> (c, DataNOTHING, ExprConstructor nlabl [head, tail])) demodfinal demodes
demodExpr env qmap (c, SynExprIfThenElse cond iftrue iffalse) = demodExpr env qmap (c, --TODO: Forse questo va "specializzato" come le implementazioni di synexprlistnil etc...
    SynExprPut cond [
        ((c, Nothing, SynPatVariant (Path ["Core"] "True") []), iftrue),
        ((c, Nothing, SynPatVariant (Path ["Core"] "False") []), iffalse)
    ])
demodExpr env qmap (c, SynExprInlineUse (Path path labl) e) = do
    env' <- getPathEnv c env (path ++ [labl])
    demodExpr (envsUnionLeft env' env) qmap e
demodExpr env qmap (c, SynExprBind pat me fe) = do
    (DemodEnv _ vs _ _ _) <- getPathEnv c env ["Core"]
    case Map.lookup "bind" vs of
        Nothing -> fail $ show c ++ " The Core module does not provide a definition for bind"
        Just (_, nlabl) -> do
            me' <- demodExpr env qmap me
            lam <- demodExpr env qmap (c, SynExprLambda pat fe)
            return (c, DataNOTHING, ExprApp (c, DataNOTHING, ExprApp (c, DataNOTHING, ExprLabel nlabl) me') lam)
demodExpr env qmap (c, SynExprHint hint e) = do
    demodhint <- demodTypeExpr env qmap hint
    demode <- demodExpr env qmap e
    return (c, DataNOTHING, ExprHint demodhint demode)

-- definizioni dei valori globali
demodTySchemeExpr :: DemodEnv -> Map.Map String TyQuant -> SyntaxTySchemeExpr -> TyperState (Map.Map String TyQuant, Qual DataType)
demodTySchemeExpr env qmap (c, qls, ps, te) = do
    (qmap', _) <- buildQmapQlist c qls
    if (length $ Map.intersection qmap qmap') /= 0
        then fail $ show c ++ " Type scheme declares already used tyquants (TODO: migliora l'error reporting)"
        else do
            ps' <- mapM (demodPred env (Map.union qmap' qmap)) ps
            te' <- demodTypeExpr env (Map.union qmap' qmap) te
            return (qmap', Qual ps' te')

demodValDef env (SynValDef c _ l t e) = do
    (qmap, t') <- case t of
        Nothing -> return (Map.empty, Nothing)
        Just te -> do
            (qmap, te') <- demodTySchemeExpr env Map.empty te
            return (qmap, Just te')
    e' <- demodExpr env qmap e
    return (ValDef c l t' [] e')

valDefGroupEnv :: DemodEnv -> [SyntaxValDef] -> TyperState (DemodEnv, [SyntaxValDef])
valDefGroupEnv env [] = return (env, [])
valDefGroupEnv env@(DemodEnv _ vs _ _ _) (SynValDef c v l t e:vvdefs)
    | Map.member l vs = fail $ show c ++ " Value: " ++ show l ++ " already bound"
    | otherwise = do
        suffix <- newUniqueSuffix
        (env', vdefs') <- valDefGroupEnv (envsUnionLeft env (DemodEnv Map.empty (Map.singleton l (visibtoenv v, l++suffix)) Map.empty Map.empty Map.empty)) vvdefs
        return (env', SynValDef c v (l++suffix) t e:vdefs')

-- definizioni dei datatype
demodTypeExprLoc env qmap (c, SynTypeExprQuantifier l) =
    case Map.lookup l qmap of
        Nothing -> fail $ show c ++ " Type quantifier: " ++ show l ++ " not bound"
        Just q -> return (False, DataCOORD c (DataQuant q))
demodTypeExprLoc env qmap (c, SynTypeExprTuple stes) = do
    (islocs, tes) <- fmap unzip $ mapM (demodTypeExprLoc env qmap) stes
    return (any id islocs, foldl (\tef tea -> DataCOORD c (DataTypeApp tef tea)) (DataCOORD c (DataTypeName (makeTupLabl $ length tes) KindNOTHING)) tes)
demodTypeExprLoc env qmap (c, SynTypeExprName pathlabl@(Path path labl)) = do
    (DemodEnv _ _ ts _ _) <- getPathEnv c env path
    case Map.lookup labl ts of
        Nothing -> fail $ show c ++ " Type label: " ++ show pathlabl ++ " not bound"
        Just (v, nlabl) -> return (isLocal v, DataCOORD c (DataTypeName nlabl KindNOTHING))
demodTypeExprLoc env qmap (c, SynTypeExprApp stef steas) = do
    (isloc, tef) <- demodTypeExprLoc env qmap stef
    (islocs, teas) <- fmap unzip $ mapM (demodTypeExprLoc env qmap) steas
    return (any id (isloc : islocs), foldl (\f a -> DataCOORD c (DataTypeApp f a)) tef teas) --TODO: Le applicazioni di typesyn vanno gestite diversamente

demodTypeExpr :: DemodEnv -> Map.Map String TyQuant -> SyntaxTypeExpr -> TyperState DataType
demodTypeExpr e q t = fmap snd $ demodTypeExprLoc e q t

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
        (env', vardefs') <- dataVarsEnv v (envsUnionLeft env (DemodEnv Map.empty Map.empty Map.empty (Map.singleton l (visibtoenv v, l++suffix)) Map.empty)) vardefs
        return (env', SynDataVariant c (l++suffix) tes:vardefs')

dataDefGroupEnv :: DemodEnv -> [SyntaxDataDef] -> TyperState (DemodEnv, [SyntaxDataDef])
dataDefGroupEnv env [] = return (env, [])
dataDefGroupEnv env@(DemodEnv _ _ ts _ _) (SynDataDef c v l qs vars:ddefs)
    | Map.member l ts = fail $ show c ++ " Data: " ++ show l ++ " already bound"
    | otherwise = do
        suffix <- newUniqueSuffix
        (env', vars') <- dataVarsEnv v env vars
        (env'', ddefs') <- dataDefGroupEnv (envsUnionLeft env' (DemodEnv Map.empty Map.empty (Map.singleton l (visibtoenv v, l++suffix)) Map.empty Map.empty)) ddefs
        return (env'', SynDataDef c v (l++suffix) qs vars':ddefs')

-- rel & inst
demodRelDecl env@(DemodEnv ms vs ts cs rs) qmap visib (c, l, tyscheme)
    | Map.member l vs = fail $ show c ++ " Value: " ++ show l ++ " already declared"
    | otherwise = do
        suffix <- newUniqueSuffix
        (_, dt) <- demodTySchemeExpr env qmap tyscheme
        return (DemodEnv ms (Map.insert l (visib, l++suffix) vs) ts cs rs, Map.singleton l (l++suffix), (c, l++suffix, dt))
demodRelDecls env qmap visib [] = return (env, Map.empty, [])
demodRelDecls env qmap visib (decl:decls) = do
    (env', relenv, decl') <- demodRelDecl env qmap visib decl
    (env'', relenv', decls') <- demodRelDecls env' qmap visib decls
    return (env'', Map.union relenv' relenv, decl':decls')

demodPredLoc env qmap (c, pathlabl@(Path path labl), steas) = do
    (DemodEnv _ _ _ _ rs) <- getPathEnv c env path
    case Map.lookup labl rs of
        Nothing -> fail $ show c ++ " Rel label: " ++ show pathlabl ++ " not bound"
        Just (v, (nlabl, _)) -> do
            (islocs, teas) <- fmap unzip $ mapM (demodTypeExprLoc env qmap) steas
            return $ (any id (isLocal v : islocs), Pred nlabl teas)
demodPred env qmap p = fmap snd $ demodPredLoc env qmap p

demodInstDefs rc env qmap relenv rpath defs = loop [] relenv defs
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
                    e' <- demodExpr env qmap e
                    loop ((c, newlabl, e'):final) (Map.delete l mrelenv) mdefs
-- moduli
type FilesEnv = Map.Map String DemodEnv

demodModDef :: DemodEnv -> DemodEnv -> FilesEnv -> SyntaxModDef -> TyperState (DemodEnv, FilesEnv, BlockProgram)
demodModDef core env@(DemodEnv ms vs ts cs rs) files (ModMod c v l m)
    | Map.member l ms = fail $ show c ++ " Module: " ++ show l ++ " already defined"
    | otherwise = do
        (menv, files', demodded) <- demodModule core (envSetPrivate env) files m
        return (DemodEnv (Map.insert l (visibtoenv v, envGetPubs menv) ms) vs ts cs rs, files', demodded)
demodModDef core env files (ModUse c v (Path p l)) =
    let setVisib = case v of
            Public -> id
            Private -> envSetPrivate
    in do
        useEnv <- getPathEnv c env (p++[l])
        return (envsUnionLeft (setVisib useEnv) env, files, BlockProgram [] [] [] [] [])
demodModDef core env@(DemodEnv ms vs ts cs rs) files (ModFromFile c v l fname)
    | Map.member l ms = fail $ show c ++ " Module: " ++ show l ++ " already defined"
    | otherwise = do
        (menv, files', block) <- demodFile fname core files
        return (DemodEnv (Map.insert l (visibtoenv v, envGetExts menv) ms) vs ts cs rs, files', block)
demodModDef core env fs (ModValGroup vvdefs) = do
    (env', vdefs) <- valDefGroupEnv env vvdefs
    vdefs' <- mapM (demodValDef env') vdefs
    return (env', fs, BlockProgram [] [] [] [vdefs'] [])
demodModDef core env fs (ModDataGroup ddefs) = do
    (env', ddefs') <- dataDefGroupEnv env ddefs
    ddefs'' <- mapM (demodDataDef env') ddefs'
    return (env', fs, BlockProgram [ddefs''] [] [] [] [])
demodModDef core env@(DemodEnv ms vs ts cs rs) fs (ModRel c visib preds l qls decls)
    | Map.member l rs = fail $ show c ++ " Rel: " ++ show l ++ " already defined"
    | otherwise = do
        suffix <- newUniqueSuffix
        (qmap, qlist) <- buildQmapQlist c qls
        preds' <- mapM (demodPred env qmap) preds
        (DemodEnv ms' vs' ts' cs' rs', relenv, decls') <- demodRelDecls env qmap (visibtoenv visib) decls
        return (DemodEnv ms' vs' ts' cs' (Map.insert l (visibtoenv visib, (l++suffix, relenv)) rs'), fs, BlockProgram [] [RelDef c (l++suffix) (map snd qlist) preds' decls'] [] [] [])
demodModDef core env fs (ModInst c qls preds head@(_, rpl@(Path rpath rlabl), _) defs) = do
    (qmap, qlist) <- buildQmapQlist c qls
    preds' <- mapM (demodPred env qmap) preds
    (isloc, pred') <- demodPredLoc env qmap head
    if isloc then return ()
    else fail $ show c ++ " There are no locally defined names in instance head: " ++ show pred'
    (DemodEnv _ _ _ _ rs) <- getPathEnv c env rpath
    let relenv = case Map.lookup rlabl rs of
            Just (_, (_, relenv)) -> relenv
    defs' <- demodInstDefs c env qmap relenv rpl defs
    return (env, fs, BlockProgram [] [] [] [] [InstDef c (Qual preds' pred') defs'])
demodModDef core env _ (ModTypeSyn _ _ _ _ _) = error "TODO demod dei typesyn. Vanno sostituiti qui o restano nel HLDefs?"
demodModDef core env@(DemodEnv ms vs ts cs rs) fs (ModExt c visib l tas tr) --TODO: Controlla se in moduli diversi vengono definiti due combinatori con lo stesso nome. FORSE BASTA USARE SEMPRE LO STESSO SUFFISSO (extSuffix)
    | Map.member l vs = fail $ show c ++ " Val: " ++ show l ++ " already defined"
    | otherwise = do
        tas' <- mapM (demodTypeExpr env Map.empty) tas
        tr' <- demodTypeExpr env Map.empty tr
        defsuffix <- newUniqueSuffix
        suffixes <- mapM (\_->newUniqueSuffix) [0..length tas-1]
        let vnames = map ("_v"++) suffixes
            ves = map (\myl->(c,DataNOTHING,ExprLabel myl)) vnames
            finale = foldr (\myl e->(c,DataNOTHING, ExprLambda (c, Just myl, PatWildcard) e)) (c, DataNOTHING, ExprCombinator l ves) vnames
        return (DemodEnv ms (Map.insert l (visibtoenv visib, l++defsuffix) vs) ts cs rs, fs, BlockProgram [] [] [ExtDef c l tas' tr'] [[ValDef c (l++defsuffix) Nothing [] finale]] [])

concatBlockPrograms (BlockProgram datagroups reldefs extdefs valgroups instdefs) (BlockProgram datagroups' reldefs' extdefs' valgroups' instdefs') = BlockProgram (datagroups++datagroups') (reldefs++reldefs') (extdefs++extdefs') (valgroups++valgroups') (instdefs++instdefs')

demodModDefs core env files [] = return (env, files, BlockProgram [] [] [] [] [])
demodModDefs core env files (def:defs) = do
    (env', files', block) <- demodModDef core env files def
    (env'', files'', block') <- demodModDefs core env' files' defs
    return (env'', files'', concatBlockPrograms block block')

demodModule :: DemodEnv -> DemodEnv -> FilesEnv -> SyntaxModule -> TyperState (DemodEnv, FilesEnv, BlockProgram)
demodModule core env files (Module defs) = demodModDefs core env files defs

demodFile :: String -> DemodEnv -> FilesEnv -> TyperState (DemodEnv, FilesEnv, BlockProgram)
demodFile fname core files = do
    handle <- lift $ lift $ openFile fname ReadMode
    contents <- lift $ lift $ hGetContents handle
    typerLog $ "File " ++ show fname ++ ": " ++ contents
    case Map.lookup contents files of
        Just modenv -> return (modenv, files, BlockProgram [] [] [] [] [])
        Nothing -> case parse getProgram (Coord fname 1 1, contents) of
            POk syntree _ -> do --TODO: non termina su moduli ciclici
                (modenv, files', block) <- demodModule core core files syntree
                return (modenv, Map.insert contents modenv files', block)
            pe -> fail $ show pe


emptyEnv = DemodEnv Map.empty Map.empty Map.empty Map.empty Map.empty

demodStdlib :: String -> String -> TyperState (DemodEnv, FilesEnv, BlockProgram)
demodStdlib corefname stdfname = do
    (coreEnv, _, coreBlock) <- demodFile corefname initCoreDemodEnv Map.empty
    let coreEnvExport = DemodEnv (Map.singleton "Core" (visibtoenv Private, envGetExts coreEnv)) Map.empty Map.empty Map.empty Map.empty
    (stdEnv, stdfiles, stdBlock) <- demodFile stdfname coreEnvExport Map.empty
    let stdEnvExport = envsUnionLeft (DemodEnv (Map.singleton "Std" (visibtoenv Private, envGetExts stdEnv)) Map.empty Map.empty Map.empty Map.empty) coreEnvExport
    return (stdEnvExport, stdfiles, concatBlockPrograms coreBlock stdBlock)

demodProgram :: String -> String -> String -> TyperState (DemodEnv, HLExpr, BlockProgram)
demodProgram corefname stdfname progfname = do
    (stdEnv, stdfiles, stdBlock) <- demodStdlib corefname stdfname
    (progEnv, progfiles, progBlock) <- demodFile progfname stdEnv stdfiles
    --typerLog $ "Final demodEnv: " ++ show modEnv
    --typerLog $ "Demodded Core: " ++ (drawTree $ toTreeBlockProgram coreBlock)
    --typerLog $ "Demodded: " ++ (drawTree $ toTreeBlockProgram modBlock)
    --typerLog $ "progEnv: " ++ show progEnv
    entryBlock <- entryPointBlock progEnv
    return (envsUnionLeft stdEnv progEnv, (Coord "entryPoint" 0 0, realworldT, ExprLabel "entryPoint#BI"), concatBlockPrograms stdBlock (concatBlockPrograms progBlock entryBlock))
