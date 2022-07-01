module TypeTyper where
import Control.Monad.Trans
import qualified Data.Map as Map
import qualified Data.Set as Set
import MPCL (StdCoord)
import TypingDefs
import MGUs
import HLDefs

getVariantData :: StdCoord -> TypingEnv -> String -> TyperState VariantData
getVariantData _ _ l@('(':')':slen) =
    let len :: Int
        len = read slen
    in do
        qs <- mapM (\_->newTyQuant KType) [1..len]
        let ts = map DataQuant qs in return $ VariantData l qs ts (buildTupType ts)
getVariantData c (TypingEnv _ _ vs _) l =
    case Map.lookup l vs of
        --Nothing -> fail $ show c ++ " Unbound constructor: " ++ l
        Just vdata -> do
            lift $ lift $ putStrLn $ "VDATA " ++ show l ++ show vdata
            return vdata

-- Funzioni di typing
typeLit :: Literal -> DataType
typeLit (LitInteger _) = intT
typeLit (LitFloating _) = fltT
typeLit (LitCharacter _) = chrT

-- Funzioni per i pattern, DA RICONTROLLARE E COMPLETARE
typePat :: TypingEnv -> HLPattern -> TyperState DataType
typePat _ (_, _, PatWildcard) = freshType KType
typePat _ (_, _, PatLiteral lit) = return $ typeLit lit
typePat env (c, _, PatVariant v ps) = do
    (VariantData _ qs vts dt) <- getVariantData c env v
    if length ps /= length vts then fail $ show c ++ " Constructor is applied to wrong number of arguments"
    else do
        s <- getInstantiationSubst qs
        pts <- mapM (typePat env) ps
        s' <- liftUnionList mgu c $ zip (map (substApply s) vts) pts --TODO questo in teoria controlla la validità degli argomenti, va rifatto, forse serve un algoritmo di unificazione "one-way"
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
typeExprInternal :: TypingEnv -> HLExpr -> TyperState (Subst, [Pred], DataType, HLExpr)
typeExprInternal _ (c, _, ExprLiteral lit) = do
    let dt = typeLit lit in return (nullSubst, [], dt, (c, dt, ExprLiteral lit))
typeExprInternal (TypingEnv env _ _ _) (c, _, ExprLabel labl) =
    case Map.lookup labl env of
        --Nothing -> fail $ show c ++ " Unbound variable: " ++ labl
        Just scheme -> do
                          lift $ lift $ putStrLn $ show c ++ " LABEL:" ++ labl ++ " of scheme:" ++ show scheme
                          Qual ps t <- instantiate scheme
                          return (nullSubst, ps, t, (c, t, ExprLabel labl))
typeExprInternal env (c, _, ExprConstructor l []) = do
    (VariantData _ qs argts dt) <- getVariantData c env l
    s <- getInstantiationSubst qs
    let mydt = substApply s (foldr buildFunType dt argts)
    lift $ lift $ putStrLn $ "CONSTRUCTOR DT " ++ show l ++ show mydt
    return (nullSubst, [], mydt, (c, mydt, ExprConstructor l []))
typeExprInternal env (c, _, ExprConstructor l es) = do --TODO: Da testare
    (s, ps, t, (_, _, ExprApp (_, _, ExprConstructor l' es') e')) <- typeExpr env (c, DataNOTHING, ExprApp (c, DataNOTHING, ExprConstructor l (init es)) (last es))
    return (s, ps, t, (c, t, ExprConstructor l' (es' ++ [e'])))
    --typeExpr env (foldl (\e0 e1 -> (c, DataNOTHING, ExprApp e0 e1)) (c, DataNOTHING, ExprConstructor l []) es)
typeExprInternal env (c, _, ExprApp f a) = do
    q <- freshType KType
    (s1, ps1, t1, f') <- typeExpr env f
    (s2, ps2, t2, a') <- typeExpr (substApply s1 env) a
    s3 <- mgu c (substApply s2 t1) (buildFunType t2 q)
    -- lift $ lift $ putStrLn $ show c ++" TypingApp s:" ++ show (composeSubst s3 (composeSubst s2 s1)) ++ " Call:" ++ show t1 ++ " with:" ++ show t2
    let finals = composeSubst s3 (composeSubst s2 s1)
        finalt = substApply finals q
        finalps = map (substApply finals) (ps1++ps2)
    return (finals, finalps, finalt, (c, finalt, ExprApp f' a'))
-- TODO: Da qui in poi controllare bene, non so se è giusto
typeExprInternal env (c, _, ExprLambda pat expr) = do
    argt <- typePat env pat
    env' <- patVarsInEnv (TyScheme [] . Qual []) env pat argt
    (s, ps, t, e) <- typeExpr env' expr
    let finaldt = buildFunType (substApply s argt) t
        in return (s, ps, finaldt, (c, finaldt, ExprLambda pat e))
typeExprInternal env (c, _, ExprPut val pses) = do
    (s, ps, tval, val') <- typeExpr env val
    (s', tval') <- unifyPats (substApply s env) tval pses
    tempt <- freshType KType--TODO GIUSTO IL FRESH?
    (s'', ps'', texpr, pses') <- typePutBranches (substApply (composeSubst s' s) env) (Qual ps tval') tempt pses
    lift $ lift $ putStrLn $ show c ++ " PUT" ++ show tempt ++ " tval:" ++ show tval' ++ " texpr:"++show texpr
    let finals = composeSubst s'' (composeSubst s' s)
        finalps = map (substApply finals) (ps++ps'')
        finalt = substApply finals texpr
        in return (finals, finalps, finalt, (c, finalt, ExprPut val' pses'))

typeExpr :: TypingEnv -> HLExpr -> TyperState (Subst, [Pred], DataType, HLExpr)
typeExpr env expr@(c, _, _) = do
    (s, ps, t, expr') <- typeExprInternal env expr
    ps' <- reduce c env ps
    --checkAmbiguousQual c env (Qual ps' t)
    return (s, ps', t, expr')

--Funzioni helper per putexpr
unifyPats :: TypingEnv -> DataType -> [(HLPattern, HLExpr)] -> TyperState (Subst, DataType)
unifyPats _ t [] = return (nullSubst, t)
unifyPats env t ((pat, (c, _, _)):branches) = do
    tpat <- typePat env pat
    s <- mgu c t tpat
    (s', t') <- unifyPats (substApply s env) (substApply s t) branches
    return (composeSubst s' s, t')

typePutBranches :: TypingEnv -> Qual DataType -> DataType -> [(HLPattern, HLExpr)] -> TyperState (Subst, [Pred], DataType, [(HLPattern, HLExpr)])
typePutBranches _ _ texpr [] = return (nullSubst, [], texpr, [])
typePutBranches env qtpat@(Qual pspat tpat) texpr ((pat, expr@(c, _, _)):branches) = do
    lift $ lift $ putStrLn $ " PUTBRANCH_SRT tpat:" ++ show tpat ++ " texpr:" ++ show texpr
    env' <- patVarsInEnv (TyScheme [] . Qual pspat) env pat tpat
    (s, psexpr, texpr', expr') <- typeExpr env' expr
    lift $ lift $ putStrLn $ " PUTBRANCH_TEX texpr: " ++ show texpr ++ " texpr':" ++ show texpr'
    s' <- mgu c texpr' texpr --TODO: è giusto l'ordine (texpr' prima)?
    mys <- return $ composeSubst s' s
    (s'', psbranches, tfinal, others) <- typePutBranches (substApply mys env) (substApply mys qtpat) (substApply s' texpr) branches
    lift $ lift $ putStrLn $ " PUTBRANCH_END tfinal:" ++ show tfinal ++ " s:" ++ show (composeSubst s'' mys)
    let finals = composeSubst s'' mys
        finalps = map (substApply finals) (psexpr++psbranches)
        in return (finals, finalps, tfinal, (pat, expr'):others)

--Sostituzioni su espressioni e definizioni, eseguite solo nel toplevel (riduci ancora il numero di applicazioni)
substApplyExpr :: Subst -> HLExpr -> HLExpr
substApplyExpr s (c, dt, ExprLiteral l) = (c, substApply s dt, ExprLiteral l)
substApplyExpr s (c, dt, ExprApp f a) = (c, substApply s dt, ExprApp (substApplyExpr s f) (substApplyExpr s a))
substApplyExpr s (c, dt, ExprLabel l) = (c, substApply s dt, ExprLabel l)
substApplyExpr s (c, dt, ExprConstructor l es) = (c, substApply s dt, ExprConstructor l (map (substApplyExpr s) es))
substApplyExpr s (c, dt, ExprLambda p e) = (c, substApply s dt, ExprLambda p (substApplyExpr s e))
substApplyExpr s (c, dt, ExprPut v psandes) = (c, substApply s dt, ExprPut (substApplyExpr s v) (map (\(p, e) -> (p, substApplyExpr s e)) psandes))

substApplyValDef s (ValDef c l t ps e) = ValDef c l t (map (substApply s) ps) (substApplyExpr s e)

--Funzioni per le definizioni globali
typeValDef env (ValDef c l t _ e) = do --TODO: Qui dimentico i predicati già presenti, dovrebbero essere spazzatura dalle tipizzazioni precedenti
    (s, ps, dt, e') <- typeExpr env e
    lift $ lift $ putStrLn $ "typed valdef: " ++ l ++ " with type: " ++ show (Qual ps dt) ++ " and subst: " ++ show s
    return (s, ValDef c l t ps e')

quantifiedValDefEnv init_env [] = return init_env
quantifiedValDefEnv env (ValDef c l _ _ _:vdefs) = do
    t <- freshType KType
    lift $ lift $ putStrLn $ show c ++ " Binding label: " ++ show l ++ " to temporary type: " ++ show t
    env' <- return $ tyBindAdd c env l (TyScheme [] (Qual [] t))
    quantifiedValDefEnv env' vdefs

typeValDefsLoop _ [] = return (nullSubst, [])
typeValDefsLoop env (vdef:vdefs) = do
    (s, vdef') <- typeValDef env vdef
    (s', vdefs') <- typeValDefsLoop (substApply s env) (map (substApplyValDef s) vdefs)
    return (composeSubst s' s, substApplyValDef s' vdef':vdefs')

addValDefsEnv env vdefs = foldl
    (\e (ValDef c l _ ps (_, t, _))->
            tyBindAdd c e l (generalize e (Qual ps t))
        ) env vdefs

unionValDefEnv (TypingEnv ts _ _ _) (ValDef c l _ ps (_, t, _)) = do
    Qual ps' tFromEnv <- case Map.lookup l ts of --TODO: Sto dimenticando i predicati, è giusto?
        Just scheme -> instantiate scheme
    s <- mgu c t tFromEnv
    lift $ lift $ putStrLn $ "union of env and vdef "++ l ++": " ++ show s
    return s

checkHintType :: StdCoord -> TypingEnv -> DataType -> DataType -> TyperState Subst
checkHintType c env typehint typet = match c typet typehint

checkHintPreds c env pshint pst = mapM checkHintPred pst
    where checkHintPred pt = if entail env pshint pt
            then return ()
            else fail $ show c ++ " Type hint qualifiers: " ++ show pshint ++ " do not entail constraint: " ++ show pt

checkValDefsHint _ [] = return nullSubst
checkValDefsHint env (ValDef c l Nothing _ _:vdefs) = checkValDefsHint env vdefs
checkValDefsHint env@(TypingEnv ts _ _ _) (ValDef c l (Just (Qual _ hint)) ps (_, t, _):vdefs) = do
    s <- checkHintType c env hint t
    s' <- checkValDefsHint (substApply s env) (map (substApplyValDef s) vdefs)
    return (composeSubst s' s)

checkValDefsHintPreds :: TypingEnv -> [HLValDef] -> TyperState [HLValDef]
checkValDefsHintPreds env vdefs = mapM checkValDefHintPreds vdefs
        where checkValDefHintPreds vdef@(ValDef _ _ Nothing _ _) = return vdef
              checkValDefHintPreds (ValDef c l hint@(Just (Qual pshint thint)) pst e) = do
                checkHintPreds c env pshint pst
                return $ ValDef c l hint pshint e

-- TODO: Quali di queste sostituzioni possono essere eliminate? (probabilmente quelle introdotte da typeValDefsLoop...)
-- TODO: Mi sa che questa funzione non dovrebbe restituire una sostituzione
typeValDefGroup env vdefs = do
    vars_env <- quantifiedValDefEnv env vdefs
    (s, vdefs') <- typeValDefsLoop vars_env vdefs
    substs <- mapM (unionValDefEnv (substApply s vars_env)) vdefs' -- Mi sa che questa cosa funziona solo perché le sostituzioni dovrebbero essere indipendenti l'una dall'altra a questo punto (cioè le due sostituzioni non contengono frecce discordanti e.g. q1->Int e q1->Flt) ... oppure è perché le sostituzioni vengono composte nel modo giusto???
    let s' = foldl (flip composeSubst) s substs
    s'' <- checkValDefsHint (substApply s' vars_env) (map (substApplyValDef s') vdefs') --TODO: La posizione è giusta?
    let sfinal = composeSubst s'' s'
        vdefs'' = map (substApplyValDef sfinal) vdefs'
        ps = concat $ map (\(ValDef _ _ _ ps _) -> ps) vdefs''
        vdefs''' = map (\(ValDef c l h _ e)->ValDef c l h ps e) vdefs''
            --lift $ lift $ putStrLn $ "Final ValDef Subst: " ++ show sfinal
    mapM (\(ValDef c _ _ ps' (_, t, _))->checkAmbiguousQual c env (Qual ps' t)) vdefs'''
    vdefs'''' <- checkValDefsHintPreds env vdefs'''
    let env' = addValDefsEnv (substApply sfinal env) vdefs''''
    if (0 == (length $ freetyvars env')) then return (sfinal, env', vdefs'''')
    else fail $ show ((\(ValDef c _ _ _ _)->c) $ head vdefs''') ++ " Ci sono delle variabili di tipo libere dopo la tipizzazione di un gruppo di valdef"

typeValDefGroups env [] = return (nullSubst, env, [])
typeValDefGroups env (vdefs:vdefss) = do
    (s, env', vdefs') <- typeValDefGroup env vdefs --TODO: forse anche questa sostituzione dopo averla applicata al contesto può essere eliminata
    (s', env'', vdefss') <- typeValDefGroups env' vdefss
    return (composeSubst s' s, env'', map (substApplyValDef s') vdefs':vdefss')

typeInstDef env@(TypingEnv _ _ _ rs) (InstDef c qh@(Qual ps h@(Pred l ts)) defs) =
    case Map.lookup l rs of
        Just (RelData qs decls _) -> do
            let instSubst = Map.fromList $ zip qs ts
                substdecls = map (\(ld, td)->(ld, substApply instSubst td)) decls
            defs' <- typeInstMembers (Map.fromList substdecls) [] defs
            return $ InstDef c qh defs'
    where typeInstMembers declmap final [] = return $ reverse final
          typeInstMembers declmap final ((dc,dl,e):members) =
                case Map.lookup dl declmap of
                    Just (Qual dps dt) -> do
                        (s, eps, te, e') <- typeExpr env e
                        s' <- checkHintType dc env dt te
                        let finals = composeSubst s' s
                            finale = substApplyExpr finals e'
                        checkHintPreds dc env (ps ++ dps) (map (substApply s') eps)
                        typeInstMembers declmap ((dc, dl, finale):final) members
typeInstDefs :: TypingEnv -> [HLInstDef] -> TyperState [HLInstDef]
typeInstDefs env = mapM (typeInstDef env)
