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

type EnvMap a = Map.Map String [(EnvVisib, a)]

data DemodEnv = DemodEnv
    (EnvMap DemodEnv) -- Mods
    (EnvMap String) -- Vals
    (EnvMap String) -- Types
    (EnvMap String) -- Constructors
    (EnvMap (String, Map.Map String String)) -- Rels
    deriving Show

envmapSingleton k v = Map.singleton k [v]
envmapInsert k v m = Map.alter alter k m
    where alter Nothing   = Just [v]
          alter (Just vs) = Just (v:vs)

envmapLookup :: Show a => String -> String -> EnvMap a -> TyperState (EnvVisib, a)
envmapLookup err l em = case Map.lookup l em of
    Nothing -> fail $ err ++ show em
    Just [] -> fail $ err ++ show em
    Just (v:[]) -> return v
    _ -> fail (err ++ ", choice is ambiguous")
envmapDefd l em = case Map.lookup l em of
    Nothing -> False
    Just [] -> False
    _ -> True

--Definizioni builtin per Demod
builtinDemodTypes = ["->", "Int", "Flt", "Bool", "Chr", "RealWorld_"]
builtinDemodVars = ["True", "False", "RealWorld_"]

buildBIDemodMap = Map.fromList . map buildBIDemod
    where buildBIDemod l = (l, [(LocPub, l++"#BI")])

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
    where filterpub = Map.filter ((0 /=) . length) . (fmap $ filter (\(v, _)->
            case v of
                LocPub -> True
                ExtPub -> True
                _ -> False
            ))
envGetExts (DemodEnv m v t c r) = envGetPubs (DemodEnv (filterpub m) (filterpub v) (filterpub t) (filterpub c) (filterpub r))
    where filterpub = fmap $ map (\(v, e)->
            (case v of
                LocPub -> ExtPub
                LocPriv -> ExtPriv
                _ -> v, e)
            )
envSetPrivate (DemodEnv m v t c r) = (DemodEnv (setpriv m) (setpriv v) (setpriv t) (setpriv c) (setpriv r))
    where setpriv = fmap $ map (\(v, e)->
            (case v of
                LocPub -> LocPriv
                ExtPub -> ExtPriv
                _ -> v, e)
            )

-- Al momento concatena le stesse definizioni, potrebbe creare duplicati (e quindi bug di falsa ambiguità), avrebbe senso vincolare a contesti disgiunti?
envsUnion :: DemodEnv -> DemodEnv -> DemodEnv
envsUnion (DemodEnv m v t c r) (DemodEnv m' v' t' c' r') = DemodEnv (myUnion m m') (myUnion v v') (myUnion t t') (myUnion c c') (myUnion r r')
    where myUnion = Map.unionWith (++)

getPathEnv :: StdCoord -> DemodEnv -> [String] -> TyperState DemodEnv
getPathEnv _ env [] = return env
getPathEnv c (DemodEnv envs _ _ _ _) (entry:path) = do
    (_, env) <- envmapLookup (show c ++ " Could not find module: " ++ show entry) entry envs
    getPathEnv c env path

-- Roba per i pattern
patValsInEnvInner _ env SynPatWildcard = return (env, PatWildcard)
patValsInEnvInner _ env (SynPatLiteral l) = return (env, PatLiteral l)
patValsInEnvInner _ env (SynPatTuple ps) = do
    (env', ps') <- patsValsInEnv env ps
    return (env', PatVariant (makeTupLabl $ length ps') ps')
patValsInEnvInner c env (SynPatVariant pathlabl@(Path path labl) ps) = do
    (DemodEnv _ _ _ cs _) <- getPathEnv c env path
    (_, nlabl) <- envmapLookup (show c ++ " Unbound constructor: " ++ show pathlabl) labl cs
    (env', ps') <- patsValsInEnv env ps
    return (env', PatVariant nlabl ps')
patValsInEnvInner c env SynPatListNil = do
    (DemodEnv _ _ _ cs _) <- getPathEnv c env ["Core"]
    (_, nlabl) <- envmapLookup (show c ++ " The Core module does not provide a definition for Nil") "Nil" cs
    return (env, PatVariant nlabl [])
patValsInEnvInner c env (SynPatListConss ps final) = do
    (DemodEnv _ _ _ cs _) <- getPathEnv c env ["Core"]
    (_, nlabl) <- envmapLookup (show c ++ " The Core module does not provide a definition for Cons") "Cons" cs
    (env', ps') <- patsValsInEnv env ps
    (env'', final') <- patValsInEnv env' final
    return $ (\(_,_,r)->(env'', r)) $ foldr (\head tail -> (c, Nothing, PatVariant nlabl [head, tail])) final' ps'
patValsInEnv env (c, Nothing, inner) = do
    (env', inner') <- patValsInEnvInner c env inner
    return (env', (c, Nothing, inner'))
patValsInEnv (DemodEnv ms vs ts cs rs) (c, Just l, inner)
    | envmapDefd l vs = fail $ show c ++ " Label: " ++ show l ++ " is already bound"
    | otherwise = do
        suffix <- newUniqueSuffix
        (env', inner') <- patValsInEnvInner c (DemodEnv ms (envmapInsert l (visibtoenv Private, l++suffix) vs) ts cs rs) inner
        return (env', (c, Just $ l++suffix, inner'))

patsValsInEnv :: DemodEnv -> [SyntaxPattern] -> TyperState (DemodEnv, [HLPattern])
patsValsInEnv env [] = return (env, [])
patsValsInEnv env (p:ps) = do
    (env', p') <- patValsInEnv env p
    (env'', ps') <- patsValsInEnv env' ps
    return (env'', p':ps')

--espressioni
demodExpr _ _ (c, SynExprLiteral l) = return (c, DataNOTHING, ExprLiteral l)
demodExpr env qmap (c, SynExprApp f a) = do
    f' <- demodExpr env qmap f
    a' <- demodExpr env qmap a
    return (c, DataNOTHING, ExprApp f' a')
demodExpr env _ (c, SynExprLabel pathlabl@(Path path labl)) = do
    (DemodEnv _ vs _ _ _) <- getPathEnv c env path
    (_, nlabl) <- envmapLookup (show c ++ " Unbound value: " ++ show pathlabl) labl vs
    return (c, DataNOTHING, ExprLabel nlabl)
demodExpr env _ (c, SynExprConstructor pathlabl@(Path path labl)) = do
    (DemodEnv _ _ _ cs _) <- getPathEnv c env path
    (_, nlabl) <- envmapLookup (show c ++ " Unbound constructor: " ++ show pathlabl) labl cs
    return (c, DataNOTHING, ExprConstructor nlabl [])
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
demodExpr env qmap (c, SynExprPut vals pses) = do
    vals' <- mapM (demodExpr env qmap) vals
    pses' <- mapM (\(pats, e)->do
        (env', pats') <- patsValsInEnv env pats
        e' <- demodExpr env' qmap e
        return (pats', e')
        ) pses
    return (c, DataNOTHING, ExprPut vals' pses')
demodExpr env _ (c, SynExprString s) = do
    (DemodEnv _ vs _ cs _) <- getPathEnv c env ["Core"]
    (_, conslabl) <- envmapLookup (show c ++ " The Core module does not provide a definition for Cons") "Cons" cs
    (_, nillabl) <- envmapLookup (show c ++ " The Core module does not provide a definition for strNil") "strNil" vs
    return $ foldr (\chr rest -> (c, DataNOTHING, ExprConstructor conslabl [(c, DataNOTHING, ExprLiteral (LitCharacter chr)), rest])) (c, DataNOTHING, ExprLabel nillabl) s
demodExpr env _ (c, SynExprListNil) = do --TODO: Forse questo si può ridurre a un demodExpr di un SynExprConstructor
    (DemodEnv _ _ _ cs _) <- getPathEnv c env ["Core"]
    (_, nlabl) <- envmapLookup (show c ++ " The Core module does not provide a definition for Nil") "Nil" cs
    return (c, DataNOTHING, ExprConstructor nlabl [])
demodExpr env qmap (c, SynExprListConss es final) = do
    (DemodEnv _ _ _ cs _) <- getPathEnv c env ["Core"]
    (_, nlabl) <- envmapLookup (show c ++ " The Core module does not provide a definition for Cons") "Cons" cs
    demodes <- mapM (demodExpr env qmap) es
    demodfinal <- demodExpr env qmap final
    return $ foldr (\head tail -> (c, DataNOTHING, ExprConstructor nlabl [head, tail])) demodfinal demodes
demodExpr env qmap (c, SynExprIfThenElse cond iftrue iffalse) = demodExpr env qmap (c, --TODO: Forse questo va "specializzato" come le implementazioni di synexprlistnil etc...
    SynExprPut [cond] [
        ([(c, Nothing, SynPatVariant (Path ["Core"] "True") [])], iftrue),
        ([(c, Nothing, SynPatVariant (Path ["Core"] "False") [])], iffalse)
    ])
demodExpr env qmap (c, SynExprInlineUse (Path path labl) e) = do
    env' <- getPathEnv c env (path ++ [labl])
    demodExpr (envsUnion env' env) qmap e
demodExpr env qmap (c, SynExprBind pat me fe) = do
    (DemodEnv _ vs _ _ _) <- getPathEnv c env ["Core"]
    (_, nlabl) <- envmapLookup (show c ++ " The Core module does not provide a definition for bind") "bind" vs
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
valDefGroupEnv env@(DemodEnv ms vs ts cs rs) (SynValDef c v l t e:vvdefs)
    | envmapDefd l vs = fail $ show c ++ " Value: " ++ show l ++ " already bound"
    | otherwise = do
        suffix <- newUniqueSuffix
        (env', vdefs') <- valDefGroupEnv (DemodEnv ms (envmapInsert l (visibtoenv v, l++suffix) vs) ts cs rs) vvdefs
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
    (v, nlabl) <- envmapLookup (show c ++ " Type label: " ++ show pathlabl ++ " not bound") labl ts
    return (isLocal v, DataCOORD c (DataTypeName nlabl KindNOTHING))
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
dataVarsEnv v env@(DemodEnv ms vs ts cs rs) (SynDataVariant c l tes:vardefs)
    | envmapDefd l cs = fail $ show c ++ " Constructor: " ++ show l ++ " already bound"
    | otherwise = do
        suffix <- newUniqueSuffix
        (env', vardefs') <- dataVarsEnv v (DemodEnv ms vs ts (envmapInsert l (visibtoenv v, l++suffix) cs) rs) vardefs
        return (env', SynDataVariant c (l++suffix) tes:vardefs')

dataDefGroupEnv :: DemodEnv -> [SyntaxDataDef] -> TyperState (DemodEnv, [SyntaxDataDef])
dataDefGroupEnv env [] = return (env, [])
dataDefGroupEnv env@(DemodEnv _ _ ts _ _) (SynDataDef c v l qs vars:ddefs)
    | envmapDefd l ts = fail $ show c ++ " Data: " ++ show l ++ " already bound"
    | otherwise = do
        suffix <- newUniqueSuffix
        (DemodEnv ms' vs' ts' cs' rs', vars') <- dataVarsEnv v env vars
        (env'', ddefs') <- dataDefGroupEnv (DemodEnv ms' vs' (envmapInsert l (visibtoenv v, l++suffix) ts') cs' rs') ddefs
        return (env'', SynDataDef c v (l++suffix) qs vars':ddefs')

-- rel & inst
demodRelDecl env@(DemodEnv ms vs ts cs rs) qmap visib (c, l, tyscheme)
    | envmapDefd l vs = fail $ show c ++ " Value: " ++ show l ++ " already declared"
    | otherwise = do
        suffix <- newUniqueSuffix
        (_, dt) <- demodTySchemeExpr env qmap tyscheme
        return (DemodEnv ms (envmapInsert l (visib, l++suffix) vs) ts cs rs, Map.singleton l (l++suffix), (c, l++suffix, dt))
demodRelDecls env qmap visib [] = return (env, Map.empty, [])
demodRelDecls env qmap visib (decl:decls) = do
    (env', relenv, decl') <- demodRelDecl env qmap visib decl
    (env'', relenv', decls') <- demodRelDecls env' qmap visib decls
    return (env'', Map.union relenv' relenv, decl':decls')

demodPredLoc env qmap (c, pathlabl@(Path path labl), steas) = do
    (DemodEnv _ _ _ _ rs) <- getPathEnv c env path
    (v, (nlabl, _)) <- envmapLookup (show c ++ " Rel label: " ++ show pathlabl ++ " not bound") labl rs
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
    | envmapDefd l ms = fail $ show c ++ " Module: " ++ show l ++ " already defined"
    | otherwise = do
        (menv, files', demodded) <- demodModule core (envSetPrivate env) files m
        return (DemodEnv (envmapInsert l (visibtoenv v, envGetPubs menv) ms) vs ts cs rs, files', demodded)
demodModDef core env files (ModUse c v (Path p l)) =
    let setVisib = case v of
            Public -> id
            Private -> envSetPrivate
    in do
        useEnv <- getPathEnv c env (p++[l])
        return (envsUnion (setVisib useEnv) env, files, BlockProgram [] [] [] [] [])
demodModDef core env@(DemodEnv ms vs ts cs rs) files (ModFromFile c v l fname)
    | envmapDefd l ms = fail $ show c ++ " Module: " ++ show l ++ " already defined"
    | otherwise = do
        (menv, files', block) <- demodFile fname core files
        return (DemodEnv (envmapInsert l (visibtoenv v, envGetExts menv) ms) vs ts cs rs, files', block)
demodModDef core env fs (ModValGroup vvdefs) = do
    (env', vdefs) <- valDefGroupEnv env vvdefs
    vdefs' <- mapM (demodValDef env') vdefs
    return (env', fs, BlockProgram [] [] [] [vdefs'] [])
demodModDef core env fs (ModDataGroup ddefs) = do
    (env', ddefs') <- dataDefGroupEnv env ddefs
    ddefs'' <- mapM (demodDataDef env') ddefs'
    return (env', fs, BlockProgram [ddefs''] [] [] [] [])
demodModDef core env@(DemodEnv ms vs ts cs rs) fs (ModRel c visib preds l qls decls)
    | envmapDefd l rs = fail $ show c ++ " Rel: " ++ show l ++ " already defined"
    | otherwise = do
        suffix <- newUniqueSuffix
        (qmap, qlist) <- buildQmapQlist c qls
        preds' <- mapM (demodPred env qmap) preds
        (DemodEnv ms' vs' ts' cs' rs', relenv, decls') <- demodRelDecls env qmap (visibtoenv visib) decls
        return (DemodEnv ms' vs' ts' cs' (envmapInsert l (visibtoenv visib, (l++suffix, relenv)) rs'), fs, BlockProgram [] [RelDef c (l++suffix) (map snd qlist) preds' decls'] [] [] [])
demodModDef core env fs (ModInst c qls preds head@(_, rpl@(Path rpath rlabl), _) defs) = do
    (qmap, qlist) <- buildQmapQlist c qls
    preds' <- mapM (demodPred env qmap) preds
    (isloc, pred') <- demodPredLoc env qmap head
    if isloc then return ()
    else fail $ show c ++ " There are no locally defined names in instance head: " ++ show pred'
    (DemodEnv _ _ _ _ rs) <- getPathEnv c env rpath
    (_, (_, relenv)) <- envmapLookup "" rlabl rs
    defs' <- demodInstDefs c env qmap relenv rpl defs
    return (env, fs, BlockProgram [] [] [] [] [InstDef c (Qual preds' pred') defs'])
demodModDef core env _ (ModTypeSyn _ _ _ _ _) = error "TODO demod dei typesyn. Vanno sostituiti qui o restano nel HLDefs?"
demodModDef core env@(DemodEnv ms vs ts cs rs) fs (ModExt c visib l tas tr) --TODO: Controlla se in moduli diversi vengono definiti due combinatori con lo stesso nome. FORSE BASTA USARE SEMPRE LO STESSO SUFFISSO (extSuffix)
    | envmapDefd l vs = fail $ show c ++ " Val: " ++ show l ++ " already defined"
    | otherwise = do
        tas' <- mapM (demodTypeExpr env Map.empty) tas
        tr' <- demodTypeExpr env Map.empty tr
        defsuffix <- newUniqueSuffix
        suffixes <- mapM (\_->newUniqueSuffix) [0..length tas-1]
        let vnames = map ("_v"++) suffixes
            ves = map (\myl->(c,DataNOTHING,ExprLabel myl)) vnames
            finale = foldr (\myl e->(c,DataNOTHING, ExprLambda (c, Just myl, PatWildcard) e)) (c, DataNOTHING, ExprCombinator l ves) vnames
        return (DemodEnv ms (envmapInsert l (visibtoenv visib, l++defsuffix) vs) ts cs rs, fs, BlockProgram [] [] [ExtDef c l tas' tr'] [[ValDef c (l++defsuffix) Nothing [] finale]] [])

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
    let coreEnvExport = DemodEnv (envmapSingleton "Core" (visibtoenv Private, envGetExts coreEnv)) Map.empty Map.empty Map.empty Map.empty
    (stdEnv, stdfiles, stdBlock) <- demodFile stdfname coreEnvExport Map.empty
    let stdEnvExport = envsUnion (DemodEnv (envmapSingleton "Std" (visibtoenv Private, envGetExts stdEnv)) Map.empty Map.empty Map.empty Map.empty) coreEnvExport
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
    return (envsUnion stdEnv progEnv, (Coord "entryPoint" 0 0, realworldT, ExprLabel "entryPoint#BI"), concatBlockPrograms stdBlock (concatBlockPrograms progBlock entryBlock))
