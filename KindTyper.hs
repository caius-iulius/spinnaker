module KindTyper where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe(isJust)
import Control.Monad.Trans
import MPCL(StdCoord)
import HLDefs
import TypingDefs
import MGUs

substApplyKindEnv s (TypingEnv ts ks vs cs rs) = TypingEnv ts (Map.map (kSubstApply s) ks) vs cs rs
--TODO: il pattern \(a,b)->(a, f b) si può sostituire con un fmap f
substApplyVariant s (DataVariant c l ts) = DataVariant c l (map (\(c,t)->(c, kSubstApply s t)) ts)
substApplyQuants s qs = map (\(l,q)->(l, kSubstApply s q)) qs
substApplyDataDef s (DataDef c l qs vs) = DataDef c l (substApplyQuants s qs) (map (substApplyVariant s) vs)
substApplyRelDecls s decls = map (\(c, l, t) -> (c, l, kSubstApply s t)) decls

-- Funzioni di typing
getTyData :: StdCoord -> TypingEnv -> String -> TyperState Kind
getTyData c (TypingEnv _ ks _ _ _) l
    | fst $ isTupLabl l = let len = snd $ isTupLabl l in
        return $ foldr (\_->KFun KType) KType [0..len - 1]
    | otherwise = case Map.lookup l ks of
        Nothing -> fail $ show c ++ " Unbound typename: " ++ l
        Just k -> return k

typeTyExpr :: StdCoord -> TypingEnv -> DataType -> TyperState (KindSubst, Kind, DataType)
typeTyExpr _ env (DataCOORD c dt) = typeTyExpr c env dt
typeTyExpr c _ (DataQuant q) =
    return (nullKSubst, kind q, DataQuant q)
{-typeTyExpr env qmap (c, TypeExprTuple exprs) = do
    (s, ts) <- typeTyExprsStar env qmap exprs
    return $ (s, KType, DataTuple ts)-}
typeTyExpr c env (DataTypeName l k) = do
    k' <- getTyData c env l
    return (nullKSubst, k', DataTypeName l k')
typeTyExpr c env (DataTypeApp f a) = do
    q <- freshKind
    (s1, k1, tf) <- typeTyExpr c env f
    (s2, k2, ta) <- typeTyExpr c env (kSubstApply s1 a)
    s3 <- kindmgu c (kSubstApply s2 k1) (KFun k2 q)
    let finals = composeKSubst s3 (composeKSubst s2 s1)
        finalk = kSubstApply s3 q in
            return (finals, finalk, DataTypeApp (kSubstApply finals tf) (kSubstApply finals ta))

typeAndUnifyList :: Kinds e => (StdCoord -> TypingEnv -> e -> TyperState (KindSubst, Kind, e)) -> TypingEnv -> [(StdCoord, e)] -> [Kind] -> TyperState (KindSubst, [(StdCoord, e)])
typeAndUnifyList tye env [] [] = return (nullKSubst, [])
typeAndUnifyList tye env ((c,e):es) (mk:ks) = do
    (s, k, t) <- tye c env e
    s' <- kindmgu c k mk
    (s'', ts) <- typeAndUnifyList tye env (map (\(c',e')->(c', kSubstApply (composeKSubst s' s) e')) es) ks
    s''' <- return $ composeKSubst s'' (composeKSubst s' s)
    return (s''', (c, kSubstApply s''' t):ts)

typeTyExprsStar env ts = typeAndUnifyList typeTyExpr env ts (take (length ts) $ repeat KType)
typeQualTypeStar env ts = typeAndUnifyList typeQualType env ts (take (length ts) $ repeat KType)

typeDataVariant env (DataVariant c l es) = do
    (s, ts) <- typeTyExprsStar env es
    return (s, DataVariant c l ts)

typeDataVariants env [] = return (nullKSubst, [])
typeDataVariants env (v:vs) = do
    (s, v') <- typeDataVariant env v
    (s', vs') <- typeDataVariants env vs
    return (composeKSubst s' s, (substApplyVariant s' v'):vs')

typeDataDef env (DataDef c l qs vs) = do
    (s, vs') <- typeDataVariants env vs
    return (s, DataDef c l qs vs')

typeDataDefsLoop :: TypingEnv -> [HLDataDef] -> TyperState (KindSubst, [HLDataDef])
typeDataDefsLoop env [] = return (nullKSubst, [])
typeDataDefsLoop env (ddef:ddefs) = do
    (s, ddef') <- typeDataDef env ddef
    (s', ddefs') <- typeDataDefsLoop (substApplyKindEnv s env) ddefs
    return (composeKSubst s' s, ddef':ddefs')

qstokind qs = foldr KFun KType $ map (kind . snd) qs

addDataDefsEnv :: TypingEnv -> [HLDataDef] -> TypingEnv
addDataDefsEnv env ddefs =
    let datadeftotype (DataDef _ l qs vs) =
            foldl DataTypeApp (DataTypeName l (qstokind qs)) (map (DataQuant . snd) qs)
        varianttovdata t qs (DataVariant _ l ts) =
            Map.singleton l (VariantData l (map snd qs) (map snd ts) t)
        getvariantdatas ddef@(DataDef _ l qs vs) =
            Map.unions $ map (varianttovdata (datadeftotype ddef) qs) vs
    in foldl (\(TypingEnv ts ks vs cs rs) ddef@(DataDef c l qs _)->
            TypingEnv ts (Map.insert l (qstokind qs) ks) (Map.union vs (getvariantdatas ddef)) cs rs
        ) env ddefs

unionDataDefEnv (TypingEnv _ ks _ _ _) (DataDef c l qs _) = 
    case Map.lookup l ks of
        Just kFromEnv -> do
            s <- kindmgu c (qstokind qs) kFromEnv
            return s

kindMonomorphize :: Kinds k => k -> KindSubst
kindMonomorphize = Map.fromList . map (flip (,) KType) . Set.toList . freeKindQuants

dataMonomorphize (DataDef _ _ qs _) = Map.unions $ map (kindMonomorphize . kind . snd) qs

typeDataDefGroup :: TypingEnv -> [HLDataDef] -> TyperState (KindSubst, TypingEnv, [HLDataDef])
typeDataDefGroup env ddefs = let datas_env =addDataDefsEnv env ddefs in do
    (s, ddefs') <- typeDataDefsLoop datas_env ddefs
    substs <- mapM (unionDataDefEnv (substApplyKindEnv s datas_env)) ddefs'
    let s' = foldl (flip composeKSubst) s substs
        ddefs'' = map (substApplyDataDef s') ddefs'
        s'' = Map.unions $ map dataMonomorphize ddefs''
        ddefs''' = map (substApplyDataDef s'') ddefs''
        s''' = composeKSubst s'' s'
        env' = addDataDefsEnv (substApplyKindEnv s''' env) ddefs''' --TODO: è necessario? se non sbaglio l'env è senza variabili
        in return (s''', env', ddefs''')

typeDataDefGroups :: TypingEnv -> [[HLDataDef]] -> TyperState (KindSubst, TypingEnv, [[HLDataDef]])
typeDataDefGroups env [] = return (nullKSubst, env, [])
typeDataDefGroups env (ddefs:ddefss) = do
    (s, env', ddefs') <- typeDataDefGroup env ddefs
    (s', env'', ddefss') <- typeDataDefGroups env' ddefss
    return (composeKSubst s' s, env'', map (substApplyDataDef s') ddefs':ddefss') --TODO: è necessaro? se non sbaglio l'env è senza variabili

typeExtDefs :: TypingEnv -> [HLExtDef] -> TyperState [HLExtDef]
typeExtDefs env edefs = mapM (\(ExtDef c l tas tr)-> do 
    (_, tr':tas') <- typeTyExprsStar env (map (\mt->(c,mt)) (tr:tas))
    --TODO controlla monomorfizzazione
    return (ExtDef c l (map snd tas') (snd tr'))) edefs

extDefsInEnv :: TypingEnv -> [HLExtDef] -> TypingEnv
extDefsInEnv env@(TypingEnv ts ks vs cs rs) edefs =
    let ltpairs = map (\(ExtDef c l tas tr) -> (l, (tas, tr))) edefs
    in TypingEnv ts ks vs (Map.union (Map.fromList ltpairs) cs) rs

typeRelDecls :: TypingEnv  -> [(StdCoord, String, Qual DataType)] -> TyperState (KindSubst, [(StdCoord, String, Qual DataType)])
typeRelDecls env decls = do
    (s, csts) <- typeQualTypeStar env (map (\(c,l,t)->(c,t)) decls)
    s' <- return $ Map.unions $ map (\(c, t) -> kindMonomorphize $ kind t) csts
    return (composeKSubst s' s, zipWith (\(_,l,_) (c, t)->(c,l, kSubstApply s' t)) decls csts)


addRel :: String -> [TyQuant] -> [Pred] ->  [(StdCoord, String, Qual DataType)] -> TypingEnv -> TypingEnv
addRel l qs preds decls (TypingEnv ts ks vs cs rs) =
    let relpred = Pred l (map DataQuant qs)
        declpairs = map (\(_,d,Qual ps t)->(d, Qual (relpred:ps) t)) decls
        in TypingEnv ts ks vs cs (Map.insert l (RelData qs preds declpairs []) rs)

typeRelDef env (RelDef c l qs preds decls) = do
    (s, preds') <- typePreds c env preds
    (s', decls') <- typeRelDecls env (substApplyRelDecls s decls)
    let s'' = Map.unions $ map (kindMonomorphize . kind . kSubstApply (composeKSubst s' s)) qs
        s''' = composeKSubst s'' (composeKSubst s' s)
        preds'' = map (substApplyPred s''') preds'
        decls'' = substApplyRelDecls s''' decls'
        qs' = map (kSubstApply s''') qs
        in return (s''', (addRel l qs' preds'' decls'' (substApplyKindEnv s''' env)), RelDef c l qs' preds'' decls'') --TODO: è necessario? se non sbaglio l'env è senza variabili.

typeRelDefs :: TypingEnv -> [HLRelDef] -> TyperState (KindSubst, TypingEnv, [HLRelDef])
typeRelDefs env [] = return (nullKSubst, env, [])
typeRelDefs env (reldef:reldefs) = do
    (s, env', reldef') <- typeRelDef env reldef
    (s', env'', reldefs') <- typeRelDefs env' reldefs
    return (composeKSubst s' s, env'', reldef':reldefs') --TODO: è necessario? se non sbaglio l'env è senza variabili. TODO: se è necessario qui c'è un bug, non viene applicata la sostituzione s' a reldef'

typePred :: StdCoord -> TypingEnv -> Pred -> TyperState (KindSubst, Pred)
typePred c env@(TypingEnv _ _ _ _ rs) (Pred l ts) =
    case Map.lookup l rs of
        Just (RelData qs _ _ _) -> do
            if length qs /= length ts
            then fail $ show c ++ " TypeRel: " ++ show l ++ " applied to wrong number of arguments"
            else do
                (s, ts') <- typeAndUnifyList typeTyExpr env (zip (take (length ts) $ repeat c) ts) (map kind qs)
                return (s, Pred l (map snd ts'))

typePreds :: StdCoord -> TypingEnv -> [Pred] -> TyperState (KindSubst, [Pred])
typePreds c env [] = return (nullKSubst, [])
typePreds c env (p:ps) = do
    (s, p') <- typePred c env p
    (s', ps') <- typePreds c env (map (substApplyPred s) ps)
    return (composeKSubst s' s, (substApplyPred s' p'):ps')

typeQualPred :: StdCoord -> TypingEnv -> Qual Pred -> TyperState (KindSubst, Qual Pred)
typeQualPred c env (Qual preds pred) = do
    (s, pred':preds') <- typePreds c env (pred:preds)
    return (s, Qual preds' pred')

typeQualType :: StdCoord -> TypingEnv -> Qual DataType -> TyperState (KindSubst, Kind, Qual DataType)
typeQualType c env (Qual preds a) = do
    (s, preds') <- typePreds c env preds
    (s', k, a') <- typeTyExpr c env (kSubstApply s a)
    return (composeKSubst s' s, k, Qual (map (substApplyPred s') preds') a')

addInst p@(Qual _ (Pred l _)) (TypingEnv ts ks vs cs rs) = TypingEnv ts ks vs cs $ Map.adjust (\(RelData qs preds decls insts)->RelData qs preds decls (p:insts)) l rs

--TODO: Sposta in altro file
--TODO: Controlla qui che non ci siano qualificatori liberi nelle definizioni
addRelDecls :: TypingEnv -> TypingEnv
addRelDecls env@(TypingEnv ts ks vs cs rs) =
    let general_decl_pairs = concat $ map (\(_, RelData _ _ lqts _)->map (\(l, qt)->(l, generalize env qt)) lqts) $ Map.toList rs
        general_decls_map = Map.fromList general_decl_pairs
        in TypingEnv (Map.union ts general_decls_map) ks vs cs rs

typeExprHints :: KindSubst -> TypingEnv -> HLExpr -> TyperState HLExpr
typeExprHints s _ (c, t, ExprLiteral l) = return (c, t, ExprLiteral l)
typeExprHints s env (c, t, ExprApp f a) = do
    f' <- typeExprHints s env f
    a' <- typeExprHints s env a
    return (c, t, ExprApp f' a')
typeExprHints s _ (c, t, ExprLabel l) = return (c, t, ExprLabel l)
typeExprHints s env (c, t, ExprConstructor l es) = do
    es' <- mapM (typeExprHints s env) es
    return (c, t, ExprConstructor l es')
typeExprHints s env (c, t, ExprCombinator l es) = do
    es' <- mapM (typeExprHints s env) es
    return (c, t, ExprCombinator l es')
typeExprHints s env (c, t, ExprLambda p e) = do
    e' <- typeExprHints s env e
    return (c, t, ExprLambda p e')
typeExprHints s env (c, t, ExprPut v pses) = do
    v' <- typeExprHints s env v
    pses' <- mapM (\(p, e) -> do {e' <- typeExprHints s env e; return (p, e')}) pses
    return (c, t, ExprPut v' pses')
typeExprHints s env (c, t, ExprHint hint e) = do
    (ks, k, hint') <- typeTyExpr c env (kSubstApply s hint)
    if length (freeKindQuants hint') == 0 then return ()
    else error "KWHAT"
    case k of
        KType -> return ()
        _ -> fail $ show c ++ " Kind of type hint should be T, instead found: " ++ show k
    e' <- typeExprHints s env e
    return (c, t, ExprHint hint' e')

typeKInstDef :: TypingEnv -> HLInstDef -> TyperState (KindSubst, TypingEnv, HLInstDef)
typeKInstDef env (InstDef c qualhead defs) = do
    (s, qualhead'@(Qual _ h@(Pred l _))) <- typeQualPred c env qualhead
    let currInsts = map (\(Qual _ mp)->mp) $ insts env l
    mapM (\i->
        if isJust (matchPred h i) && isJust (matchPred i h)
            then fail $ show c ++ " L'istanza " ++ show qualhead' ++ " è identica a un'altra già definita: " ++ show i
            else return ()
        ) currInsts
    --TODO: monomorfizzazione del qualhead
    defs' <- mapM (\(c,l,e)->do
        e' <- typeExprHints s env e
        return (c, l, e')
        ) defs
    return (s, addInst qualhead' env, InstDef c qualhead' defs')
    --TODO: controlli vari su defs (e.g. condizioni Paterson), applica la sostituzione su defs se aggiungo i cast nelle espressioni

typeKInstDefs :: TypingEnv -> [HLInstDef] -> TyperState (KindSubst, TypingEnv, [HLInstDef])
typeKInstDefs env [] = return (nullKSubst, env, [])
typeKInstDefs env (instdef:instdefs) = do
    (s, env', instdef') <- typeKInstDef env instdef
    (s', env'', instdefs') <- typeKInstDefs env' instdefs
    return (composeKSubst s' s, env'', instdef':instdefs') --TODO: è necessario? se non sbaglio l'env è senza variabili. TODO: se è necessario qui c'è un bug, non viene applicata la sostituzione s' a instdef'

-- Typing degli hint
typeValDefHint :: TypingEnv -> HLValDef -> TyperState HLValDef
typeValDefHint env vdef@(ValDef c l Nothing ps e) = do
    e' <- typeExprHints Map.empty env e
    return $ ValDef c l Nothing ps e'
typeValDefHint env (ValDef c l (Just tyscheme) ps e) = do
    (_, _, dt) <- typeQualType c env tyscheme
    s <- kindmgu c (kind dt) KType
    let s' = kindMonomorphize (kSubstApply s dt)
        s'' = composeKSubst s' s
    e' <- typeExprHints s'' env e
    typerLog $ show c ++" ValDef " ++ show l ++ " has type hint: " ++ show (kSubstApply s dt) ++ show (freeKindQuants dt)
    return $ ValDef c l (Just (kSubstApply s'' dt)) ps e'

typeValDefHints :: TypingEnv -> [[HLValDef]] -> TyperState [[HLValDef]]
typeValDefHints env vdefss = mapM (mapM $ typeValDefHint env) vdefss
