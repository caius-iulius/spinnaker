module KindTyper where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Except
import MPCL(StdCoord)
import TypingDefs
import SyntaxDefs

type KindSubst = Map.Map KindQuant Kind
nullKSubst :: KindSubst
nullKSubst = Map.empty

freeKindQuants KStar = Set.empty
freeKindQuants (KindQuant q) = Set.singleton q
freeKindQuants (KFun k k') = Set.union (freeKindQuants k) (freeKindQuants k')

-- Classe kinds, usata per sostituzioni e per avere il kind
class Kinds t where
    kind :: t->Kind
    kindSubstApply :: KindSubst -> t -> t

instance Kinds Kind where
    kind = id
    kindSubstApply _ KStar = KStar
    kindSubstApply s (KindQuant q) = case Map.lookup q s of
        Nothing -> KindQuant q
        Just k -> k
    kindSubstApply s (KFun a r) = KFun (kindSubstApply s a) (kindSubstApply s r)

instance Kinds TyQuant where
    kind (TyQuant _ k) = k
    kindSubstApply s (TyQuant t k) = TyQuant t (kindSubstApply s k)

instance Kinds DataType where
    kind (DataQuant q) = kind q
    kind (DataTuple _) = KStar
    kind (DataTypeName _ k) = k
    kind (DataTypeApp t _) = let (KFun _ k) = kind t in k
    kindSubstApply s (DataQuant q) = DataQuant (kindSubstApply s q)
    kindSubstApply s (DataTuple ts) = DataTuple (map (kindSubstApply s) ts)
    kindSubstApply s (DataTypeName l k) = DataTypeName l (kindSubstApply s k)
    kindSubstApply s (DataTypeApp t1 t2) = DataTypeApp (kindSubstApply s t1) (kindSubstApply s t2)

--substApplyKindEnv s (TypingEnv ts ks vs) = TypingEnv ts (Map.map (kindSubstApply s) ks) vs
substApplyQmap s qmap = Map.map (\(TyQuant q k)->TyQuant q (kindSubstApply s k)) qmap
substApplyVariant s (DataVariant c l tses) = DataVariant c l (map (\(t,e)->(kindSubstApply s t, e)) tses)

composeKSubst s1 s2 = Map.union (Map.map (kindSubstApply s1) s2) s1

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
kindmgu _ KStar KStar = return nullKSubst
kindmgu c (KFun a r) (KFun a' r') = do
    s1 <- kindmgu c a a'
    s2 <- kindmgu c (kindSubstApply s1 r) (kindSubstApply s1 r')
    return $ composeKSubst s1 s2
kindmgu c k1 k2 = throwError $ show c ++ " Cannot unify kinds: " ++ show k1 ++ " and " ++ show k2
{-
-- Funzioni di typing
typeTyExpr :: TypingEnv -> Map.Map String TyQuant -> SyntaxTypeExpr -> TyperState (KindSubst, Kind, DataType)
typeTyExpr _ qmap (c, TypeExprQuantifier l) =
    case Map.lookup l qmap of
        Nothing -> throwError $ show c ++ " Unbound quantifier: " ++ l
        Just q@(TyQuant _ k) -> return (nullKSubst, k, DataQuant q)
typeTyExpr env qmap (c, TypeExprTuple exprs) = do
    (s, ts) <- typeTyExprsStar env qmap exprs
    return $ (s, KStar, DataTuple ts)
typeTyExpr (TypingEnv _ env _) _ (c, TypeExprName l) =
    case Map.lookup l env of
        Nothing -> throwError $ show c ++ " Unbound type name: " ++ l
        Just k -> return (nullKSubst, k, DataTypeName l k)
typeTyExpr env qmap (c, TypeExprApp f a) = do
    q <- freshKind
    (s1, k1, tf) <- typeTyExpr env qmap f
    (s2, k2, ta) <- typeTyExpr env (substApplyQmap s1 qmap) a
    s3 <- kindmgu c (kindSubstApply s2 k1) (KFun k2 q)
    let finals = composeKSubst s3 (composeKSubst s2 s1)
        finalk = kindSubstApply s3 q in
            return (finals, finalk, DataTypeApp (kindSubstApply finals tf) (kindSubstApply finals ta))

typeTyExprsStar env qmap [] = return (nullKSubst, [])
typeTyExprsStar env qmap (e@(c,_):es) = do
    (s, k, t) <- typeTyExpr env qmap e
    s1 <- kindmgu c k KStar
    (s2, ts) <- typeTyExprsStar env (substApplyQmap (composeKSubst s1 s) qmap) es
    return (composeKSubst s2 (composeKSubst s1 s), (kindSubstApply s2 t):ts)

typeDataVariant env qmap (DataVariant c l tses) = let es = map snd tses in do
    (s, ts) <- typeTyExprsStar env qmap es
    return (s, DataVariant c l (zip ts es))

typeDataVariants env qmap [] = return (nullKSubst, [])
typeDataVariants env qmap (v:vs) = do
    (s, v') <- typeDataVariant env qmap v
    (s', vs') <- typeDataVariants env (substApplyQmap s qmap) vs
    return (composeKSubst s' s, (substApplyVariant s' v'):vs')
-}
