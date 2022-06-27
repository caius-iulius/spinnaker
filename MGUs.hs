module MGUs where
import qualified Data.Map as Map
import qualified Data.Set as Set
import MPCL(StdCoord)
import TypingDefs

-- MGU per i kinds
instance Kinds Kind where
    kind = id
    kSubstApply _ KType = KType
    kSubstApply s (KindQuant q) = case Map.lookup q s of
        Nothing -> KindQuant q
        Just k -> k
    kSubstApply s (KFun a r) = KFun (kSubstApply s a) (kSubstApply s r)
    kSubstApply _ KindNOTHING = KindNOTHING

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
    kSubstApply s (DataCOORD c t) = DataCOORD c (kSubstApply s t)

nullKSubst :: KindSubst
nullKSubst = Map.empty

freeKindQuants KType = Set.empty
freeKindQuants (KindQuant q) = Set.singleton q
freeKindQuants (KFun k k') = Set.union (freeKindQuants k) (freeKindQuants k')

composeKSubst s1 s2 = Map.union (Map.map (kSubstApply s1) s2) s1

kindQBind :: StdCoord -> KindQuant -> Kind -> TyperState KindSubst
kindQBind c kq t | t == KindQuant kq = return nullKSubst
                 | Set.member kq (freeKindQuants t) = fail $ show c ++ " Occurs check fails in kind inference: " ++ show (KindQuant kq) ++ " and " ++ show t
                 | otherwise = return $ Map.singleton kq t

kindmgu :: StdCoord -> Kind -> Kind -> TyperState KindSubst
kindmgu c (KindQuant kq) t = kindQBind c kq t
kindmgu c t (KindQuant kq) = kindQBind c kq t
kindmgu _ KType KType = return nullKSubst
kindmgu c (KFun a r) (KFun a' r') = do
    s1 <- kindmgu c a a'
    s2 <- kindmgu c (kSubstApply s1 r) (kSubstApply s1 r')
    return $ composeKSubst s1 s2
kindmgu c k1 k2 = fail $ show c ++ " Cannot unify kinds: " ++ show k1 ++ " and " ++ show k2

-- MGU per i tipi
instance Types DataType where
    freetyvars (DataQuant q) = Set.singleton q
    freetyvars (DataTypeName _ _) = Set.empty
    freetyvars (DataTypeApp dta dtb) = Set.union (freetyvars dta) (freetyvars dtb)

    substApply s (DataQuant q) = case Map.lookup q s of
        Nothing -> DataQuant q
        Just t -> t
    substApply s (DataTypeApp dta dtb) =
        DataTypeApp (substApply s dta) (substApply s dtb)
    substApply s (DataTypeName tn k) = (DataTypeName tn k)

instance Types Pred where
    freetyvars (Pred _ ts) = Set.unions $ map freetyvars ts
    substApply s (Pred l ts) = Pred l $ map (substApply s) ts

instance Types t => Types (Qual t) where
    freetyvars (Qual ps t) = Set.unions $ (freetyvars t):(map freetyvars ps)
    substApply s (Qual ps t) = Qual (map (substApply s) ps) (substApply s t)

instance Types TyScheme where
    freetyvars (TyScheme qs dt) = Set.difference (freetyvars dt) (Set.fromList qs)
    substApply s (TyScheme qs dt) = TyScheme qs (substApply (foldr Map.delete s qs) dt)

instance Types TypingEnv where
    freetyvars (TypingEnv ts _ _ _) = Set.unions $ map freetyvars (Map.elems ts)
    substApply s (TypingEnv ts ks vs rs) = TypingEnv (Map.map (substApply s) ts) ks vs rs


composeSubst sa sb = Map.union (Map.map (substApply sa) sb) sa

nullSubst :: Subst
nullSubst = Map.empty

--Algoritmo MGU
quantBind :: MonadFail m => StdCoord -> TyQuant -> DataType -> m Subst
quantBind c q t
    | (case t of
        DataQuant q' -> q' == q
        _ -> False) = return nullSubst
    | Set.member q (freetyvars t) = fail $ show c ++ " Occurs check fails: " ++ show q ++ " into " ++ show t
    | kind q /= kind t = fail $ show c ++ " Kinds do not match in substitution: " ++ show q ++ "into " ++ show t
    | otherwise = return (Map.singleton q t)

mgu :: MonadFail m => StdCoord -> DataType -> DataType -> m Subst
--TODO: regole per resilienza DataCOORD?
mgu c (DataQuant q) t = quantBind c q t
mgu c t (DataQuant q) = quantBind c q t
mgu c t@(DataTypeName s k) t'@(DataTypeName s' k') =
    if s == s'  && k == k' then return nullSubst else fail $ show c ++ " Could not unify typenames: " ++ show t ++ " and " ++ show t'
mgu c (DataTypeApp f a) (DataTypeApp f' a') = do
    s <- mgu c f f'
    s' <- mgu c (substApply s a) (substApply s a')
    return (composeSubst s' s)
mgu c t t' =
    fail $ show c ++ " Could not unify types: " ++ show t ++ " and " ++ show t'

liftUnionList :: MonadFail m => (StdCoord -> DataType -> DataType -> m Subst) -> StdCoord -> [(DataType, DataType)] -> m Subst
liftUnionList m c tts =
    foldl (\m_subst (dta, dtb) -> do{
        s <- m_subst;
        s' <- m c (substApply s dta) (substApply s dtb);
        return $ composeSubst s' s
    }) (return nullSubst) tts

--TODO: Da testare
match c src tgt = do
    s <- mgu c src tgt
    let
        keyss = Set.fromList $ map fst $ Map.toList s
        frees = freetyvars tgt
        transformsInTgt = Set.intersection keyss frees
        in if length transformsInTgt /= 0
        then fail $ show c ++ " Could not merge type: " ++ show src ++ " into: " ++ show tgt
        else return s
