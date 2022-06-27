module KindTyper where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Trans
import MPCL(StdCoord)
import HLDefs
import TypingDefs
import MGUs

substApplyKindEnv s (TypingEnv ts ks vs rs) = TypingEnv ts (Map.map (kSubstApply s) ks) vs rs
--TODO: il pattern \(a,b)->(a, f b) si può sostituire con un fmap f
substApplyVariant s (DataVariant c l ts) = DataVariant c l (map (\(c,t)->(c, kSubstApply s t)) ts)
substApplyQuants s qs = map (\(l,q)->(l, kSubstApply s q)) qs
substApplyDataDef s (DataDef c l qs vs) = DataDef c l (substApplyQuants s qs) (map (substApplyVariant s) vs)
substApplyRelDecls s decls = map (\(c, l, t) -> (c, l, kSubstApply s t)) decls
substApplyPred s (Pred l ts) = Pred l $ map (kSubstApply s) ts

-- Funzioni di typing
getTyData :: StdCoord -> TypingEnv -> String -> TyperState Kind
getTyData _ _ l@('(':')':slen) =
    let len::Int
        len = read slen
    in return $
        foldr (\_->KFun KType) KType [0..len - 1]
getTyData c (TypingEnv _ ks _ _) l =
    case Map.lookup l ks of
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

{-typeTyExprStar c env dt = do
    (s, k, dt') <- typeTyExpr c env dt
    s' <- kindmgu c k KType
    return (composeKSubst s' s, kSubstApply s' dt')-}

typeAndUnifyList :: TypingEnv -> [(StdCoord, DataType)] -> [Kind] -> TyperState (KindSubst, [(StdCoord, DataType)])
typeAndUnifyList env [] [] = return (nullKSubst, [])
typeAndUnifyList env ((c,e):es) (mk:ks) = do
    (s, k, t) <- typeTyExpr c env e
    s' <- kindmgu c k mk
    (s'', ts) <- typeAndUnifyList env (map (\(c',e')->(c', kSubstApply (composeKSubst s' s) e')) es) ks
    s''' <- return $ composeKSubst s'' (composeKSubst s' s)
    return (s''', (c, kSubstApply s''' t):ts)

typeTyExprsStar :: TypingEnv -> [(StdCoord, DataType)] -> TyperState (KindSubst, [(StdCoord, DataType)])
typeTyExprsStar env [] = return (nullKSubst, [])
{-typeTyExprsStar env ((c,e):es) = do
    (s, k, t) <- typeTyExpr c env e
    s1 <- kindmgu c k KType
    (s2, ts) <- typeTyExprsStar env es
    return (composeKSubst s2 (composeKSubst s1 s), (c, kSubstApply (composeKSubst s2 s1) t):ts)-}
{-typeTyExprsStar env ((c,e):es) = do
    (s, t) <- typeTyExprStar c env e
    (s', ts) <- typeTyExprsStar env (map (\(c',e')->(c',kSubstApply s e')) es)
    return (composeKSubst s' s, (c, kSubstApply s' t):ts)-}
typeTyExprsStar env ts = typeAndUnifyList env ts (take (length ts) $ repeat KType)

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
    in foldl (\(TypingEnv ts ks vs rs) ddef@(DataDef c l qs _)->
            TypingEnv ts (Map.insert l (qstokind qs) ks) (Map.union vs (getvariantdatas ddef)) rs
        ) env ddefs

unionDataDefEnv (TypingEnv _ ks _ _) (DataDef c l qs _) = 
    case Map.lookup l ks of
        Just kFromEnv -> do
            s <- kindmgu c (qstokind qs) kFromEnv
            return s

kindMonomorphize :: Kind -> KindSubst
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


typeRelDecls :: TypingEnv  -> [(StdCoord, String, DataType)] -> TyperState (KindSubst, [(StdCoord, String, DataType)])
typeRelDecls env decls = do
    (s, csts) <- typeTyExprsStar env (map (\(c,l,t)->(c,t)) decls)
    s' <- return $ Map.unions $ map (\(c, t) -> kindMonomorphize $ kind t) csts
    return (composeKSubst s' s, zipWith (\(_,l,_) (c, t)->(c,l, kSubstApply s' t)) decls csts)


addRel :: String -> [TyQuant] -> [(StdCoord, String, DataType)] -> TypingEnv -> TypingEnv
addRel l qs decls (TypingEnv ts ks vs rs) =
    let relpred = Pred l (map DataQuant qs)
        declpairs = map (\(_,d,t)->(d, Qual [relpred] t)) decls
        in TypingEnv ts ks vs (Map.insert l (RelData qs declpairs []) rs)

typeRelDef env (RelDef c l qs decls) = do
    (s, decls') <- typeRelDecls env decls
    let s' = Map.unions $ map (kindMonomorphize . kind . kSubstApply s) qs
        s'' = composeKSubst s' s
        decls'' = substApplyRelDecls s'' decls'
        qs' = map (kSubstApply s'') qs
        in return (s'', substApplyKindEnv s'' (addRel l qs' decls'' env), RelDef c l qs' decls'') --TODO: è necessario? se non sbaglio l'env è senza variabili.

typeRelDefs :: TypingEnv -> [HLRelDef] -> TyperState (KindSubst, TypingEnv, [HLRelDef])
typeRelDefs env [] = return (nullKSubst, env, [])
typeRelDefs env (reldef:reldefs) = do
    (s, env', reldef') <- typeRelDef env reldef
    (s', env'', reldefs') <- typeRelDefs env' reldefs
    return (composeKSubst s' s, env'', reldef':reldefs') --TODO: è necessario? se non sbaglio l'env è senza variabili. TODO: se è necessario qui c'è un bug, non viene applicata la sostituzione s' a reldef'

typePred :: StdCoord -> TypingEnv -> Pred -> TyperState (KindSubst, Pred)
typePred c env@(TypingEnv _ _ _ rs) (Pred l ts) =
    case Map.lookup l rs of
        Just (RelData qs _ _) -> do
            (s, ts') <- typeAndUnifyList env (zip (take (length ts) $ repeat c) ts) (map kind qs)
            return (s, Pred l (map snd ts'))

typeQualPred :: StdCoord -> TypingEnv -> Qual Pred -> TyperState (KindSubst, Qual Pred)
typeQualPred c env (Qual preds pred) = do
    (s, pred':preds') <- typePreds c env (pred:preds)
    return (s, Qual preds' pred')
        where   typePreds :: StdCoord -> TypingEnv -> [Pred] -> TyperState (KindSubst, [Pred])
                typePreds c env [] = return (nullKSubst, [])
                typePreds c env (p:ps) = do
                    (s, p') <- typePred c env p
                    (s', ps') <- typePreds c env (map (substApplyPred s) ps)
                    return (composeKSubst s' s, (substApplyPred s' p'):ps')

addInst p@(Qual _ (Pred l _)) (TypingEnv ts ks vs rs) = TypingEnv ts ks vs $ Map.adjust (\(RelData qs decls insts)->RelData qs decls (p:insts)) l rs

typeKInstDef :: TypingEnv -> HLInstDef -> TyperState (KindSubst, TypingEnv, HLInstDef)
typeKInstDef env (InstDef c qualhead defs) = do
    (s, qualhead') <- typeQualPred c env qualhead
    return (s, addInst qualhead env, InstDef c qualhead' defs)
    --TODO: controlli vari su defs (e.g. condizioni Paterson), applica la sostituzione su defs se aggiungo i cast nelle espressioni

typeKInstDefs :: TypingEnv -> [HLInstDef] -> TyperState (KindSubst, TypingEnv, [HLInstDef])
typeKInstDefs env [] = return (nullKSubst, env, [])
typeKInstDefs env (instdef:instdefs) = do
    (s, env', instdef') <- typeKInstDef env instdef
    (s', env'', instdefs') <- typeKInstDefs env' instdefs
    return (composeKSubst s' s, env'', instdef':instdefs') --TODO: è necessario? se non sbaglio l'env è senza variabili. TODO: se è necessario qui c'è un bug, non viene applicata la sostituzione s' a instdef'

-- Typing degli hint
typeValDefHint :: TypingEnv -> HLValDef -> TyperState HLValDef
typeValDefHint env vdef@(ValDef _ _ Nothing _ _) = return vdef
typeValDefHint env (ValDef c l (Just tyscheme) ps e) = do
    (_, _, dt) <- typeTyExpr c env tyscheme
    lift $ lift $ putStrLn $ show c ++" ValDef " ++ show l ++ " has type hint: " ++ show dt
    s <- kindmgu c (kind dt) KType
    return $ ValDef c l (Just (kSubstApply s dt)) ps e

typeValDefHints :: TypingEnv -> [[HLValDef]] -> TyperState [[HLValDef]]
typeValDefHints env vdefss = mapM (mapM $ typeValDefHint env) vdefss
