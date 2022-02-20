module KindTyper where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Except
import MPCL(StdCoord)
import TypingDefs
import HLDefs

type KindSubst = Map.Map KindQuant Kind
nullKSubst :: KindSubst
nullKSubst = Map.empty

freeKindQuants KType = Set.empty
freeKindQuants (KindQuant q) = Set.singleton q
freeKindQuants (KFun k k') = Set.union (freeKindQuants k) (freeKindQuants k')

-- Classe kinds, usata per sostituzioni e per avere il kind
class Kinds t where
    kind :: t->Kind
    kSubstApply :: KindSubst -> t -> t

instance Kinds Kind where
    kind = id
    kSubstApply _ KType = KType
    kSubstApply s (KindQuant q) = case Map.lookup q s of
        Nothing -> KindQuant q
        Just k -> k
    kSubstApply s (KFun a r) = KFun (kSubstApply s a) (kSubstApply s r)

instance Kinds TyQuant where
    kind (TyQuant _ k) = k
    kSubstApply s (TyQuant t k) = TyQuant t (kSubstApply s k)

instance Kinds DataType where
    kind (DataQuant q) = kind q
    --kind (DataTuple _) = KType
    kind (DataTypeName _ k) = k
    kind (DataTypeApp t _) = let (KFun _ k) = kind t in k
    kSubstApply s (DataQuant q) = DataQuant (kSubstApply s q)
    --kSubstApply s (DataTuple ts) = DataTuple (map (kSubstApply s) ts)
    kSubstApply s (DataTypeName l k) = DataTypeName l (kSubstApply s k)
    kSubstApply s (DataTypeApp t1 t2) = DataTypeApp (kSubstApply s t1) (kSubstApply s t2)

substApplyKindEnv s (TypingEnv ts ks vs) = TypingEnv ts (Map.map (kSubstApply s) ks) vs
--TODO: il pattern \(a,b)->(a, f b) si può sostituire con un fmap f
substApplyVariant s (DataVariant c l ts) = DataVariant c l (map (\(e,t)->(e, kSubstApply s t)) ts)
substApplyDataDef s (DataDef c l qs vs) = DataDef c l (map (\(l,q)->(l, kSubstApply s q)) qs) (map (substApplyVariant s) vs)

composeKSubst s1 s2 = Map.union (Map.map (kSubstApply s1) s2) s1

kindQBind :: StdCoord -> KindQuant -> Kind -> TyperState KindSubst
kindQBind c kq t | t == KindQuant kq = return nullKSubst
                 | Set.member kq (freeKindQuants t) = throwError $ show c ++ " Occurs check fails in kind inference: " ++ show (KindQuant kq) ++ " and " ++ show t
                 | otherwise = return $ Map.singleton kq t

kindBindAdd :: StdCoord -> TypingEnv -> String -> Kind -> TyperState TypingEnv
kindBindAdd c (TypingEnv ts ks vs) labl kind =
    case Map.lookup labl ts of
        Just _ -> throwError $ show c ++ " Type already bound " ++ labl
        Nothing -> do
            return $ TypingEnv ts (Map.union ks (Map.singleton labl kind)) vs

kindmgu :: StdCoord -> Kind -> Kind -> TyperState KindSubst
kindmgu c (KindQuant kq) t = kindQBind c kq t
kindmgu c t (KindQuant kq) = kindQBind c kq t
kindmgu _ KType KType = return nullKSubst
kindmgu c (KFun a r) (KFun a' r') = do
    s1 <- kindmgu c a a'
    s2 <- kindmgu c (kSubstApply s1 r) (kSubstApply s1 r')
    return $ composeKSubst s1 s2
kindmgu c k1 k2 = throwError $ show c ++ " Cannot unify kinds: " ++ show k1 ++ " and " ++ show k2

-- Funzioni di typing
getTyData :: StdCoord -> TypingEnv -> String -> TyperState Kind
getTyData _ _ l@('(':')':slen) =
    let len::Int
        len = read slen
    in return $
        foldr (\_->KFun KType) KType [0..len - 1]
getTyData c (TypingEnv _ ts _) l =
    case Map.lookup l ts of
        Nothing -> throwError $ show c ++ " Unbound typename: " ++ l
        Just k -> return k

typeTyExpr :: TypingEnv -> HLTypeExpr -> TyperState (KindSubst, Kind, DataType)
typeTyExpr _ (c, TypeExprQuant q) =
    return (nullKSubst, kind q, DataQuant q)
{-typeTyExpr env qmap (c, TypeExprTuple exprs) = do
    (s, ts) <- typeTyExprsStar env qmap exprs
    return $ (s, KType, DataTuple ts)-}
typeTyExpr env (c, TypeExprName l) = do
    k <- getTyData c env l
    return (nullKSubst, k, DataTypeName l k)
typeTyExpr env (c, TypeExprApp f a) = do
    q <- freshKind
    (s1, k1, tf) <- typeTyExpr env f
    (s2, k2, ta) <- typeTyExpr env a
    s3 <- kindmgu c (kSubstApply s2 k1) (KFun k2 q)
    let finals = composeKSubst s3 (composeKSubst s2 s1)
        finalk = kSubstApply s3 q in
            return (finals, finalk, DataTypeApp (kSubstApply finals tf) (kSubstApply finals ta))

typeTyExprsStar env [] = return (nullKSubst, [])
typeTyExprsStar env (e@(c,_):es) = do
    (s, k, t) <- typeTyExpr env e
    s1 <- kindmgu c k KType
    (s2, ts) <- typeTyExprsStar env es
    return (composeKSubst s2 (composeKSubst s1 s), (kSubstApply s2 t):ts)

typeDataVariant env (DataVariant c l ests) = let es = map fst ests in do
    (s, ts) <- typeTyExprsStar env es
    return (s, DataVariant c l (zip es ts))

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
        varianttovdata t qs (DataVariant _ l ests) =
            Map.singleton l (VariantData l (map snd qs) (map snd ests) t)
        getvariantdatas ddef@(DataDef _ l qs vs) =
            Map.unions $ map (varianttovdata (datadeftotype ddef) qs) vs
    in foldl (\(TypingEnv ts ks vs) ddef@(DataDef c l qs _)->
            (TypingEnv ts (Map.union ks (Map.singleton l (qstokind qs))) (Map.union vs (getvariantdatas ddef)))
        ) env ddefs

unionDataDefEnv (TypingEnv _ ks _) (DataDef c l qs _) = 
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
