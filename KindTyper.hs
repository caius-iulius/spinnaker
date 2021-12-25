module KindTyper where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Except
import MPCL(StdCoord)
import HIRDefs
import TypingDefs

type KindSubst = Map.Map KindQuant Kind
nullKSubst :: KindSubst
nullKSubst = Map.empty

freeKindQuants KindConcrete = Set.empty
freeKindQuants (KindQuant q) = Set.singleton q
freeKindQuants (KindFunction k k') = Set.union (freeKindQuants k) (freeKindQuants k')

substApplyKind :: KindSubst -> Kind -> Kind
substApplyKind _ KindConcrete = KindConcrete
substApplyKind s (KindQuant q) = case Map.lookup q s of
    Nothing -> KindQuant q
    Just k -> k
substApplyKind s (KindFunction a r) = KindFunction (substApplyKind s a) (substApplyKind s r)

--substApplyKindEnv s (TypingEnv ts ks vs) = TypingEnv ts (Map.map (substApplyKind s) ks) vs
substApplyQmap s qmap = Map.map (\(TyQuant q k)->TyQuant q (substApplyKind s k)) qmap

substApplyData s (DataQuant (TyQuant q k)) = DataQuant (TyQuant q (substApplyKind s k))
substApplyData s (DataTuple ts) = DataTuple (map (substApplyData s) ts)
substApplyData s (DataTypeName l k) = DataTypeName l (substApplyKind s k)
substApplyData s (DataTypeApp t1 t2) = DataTypeApp (substApplyData s t1) (substApplyData s t2)

substApplyVariant s (DataVariant c l tses) = DataVariant c l (map (\(t,e)->(substApplyData s t, e)) tses)

composeKSubst s1 s2 = Map.union (Map.map (substApplyKind s1) s2) s1


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
kindmgu _ KindConcrete KindConcrete = return nullKSubst
kindmgu c (KindFunction a r) (KindFunction a' r') = do
    s1 <- kindmgu c a a'
    s2 <- kindmgu c (substApplyKind s1 r) (substApplyKind s1 r')
    return $ composeKSubst s1 s2
kindmgu c k1 k2 = throwError $ show c ++ " Cannot unify kinds: " ++ show k1 ++ " and " ++ show k2

-- Funzioni di typing
typeTyExpr :: TypingEnv -> Map.Map String TyQuant -> HIRTypeExpr -> TyperState (KindSubst, Kind, DataType)
typeTyExpr _ qmap (c, TypeExprQuantifier l) =
    case Map.lookup l qmap of
        Nothing -> throwError $ show c ++ " Unbound quantifier: " ++ l
        Just q@(TyQuant _ k) -> return (nullKSubst, k, DataQuant q)
typeTyExpr env qmap (c, TypeExprTuple exprs) = do
    (s, ts) <- typeTyExprsConcrete env qmap exprs
    return $ (s, KindConcrete, DataTuple ts)
typeTyExpr (TypingEnv _ env _) _ (c, TypeExprName l) =
    case Map.lookup l env of
        Nothing -> throwError $ show c ++ " Unbound type name: " ++ l
        Just k -> return (nullKSubst, k, DataTypeName l k)
typeTyExpr env qmap (c, TypeExprApp f a) = do
    q <- freshKind
    (s1, k1, tf) <- typeTyExpr env qmap f
    (s2, k2, ta) <- typeTyExpr env (substApplyQmap s1 qmap) a
    s3 <- kindmgu c (substApplyKind s2 k1) (KindFunction k2 q)
    let finals = composeKSubst s3 (composeKSubst s2 s1)
        finalk = substApplyKind s3 q in
            return (finals, finalk, DataTypeApp (substApplyData finals tf) (substApplyData finals ta))

typeTyExprsConcrete env qmap [] = return (nullKSubst, [])
typeTyExprsConcrete env qmap (e@(c,_):es) = do
    (s, k, t) <- typeTyExpr env qmap e
    s1 <- kindmgu c k KindConcrete
    (s2, ts) <- typeTyExprsConcrete env (substApplyQmap (composeKSubst s1 s) qmap) es
    return (composeKSubst s2 (composeKSubst s1 s), (substApplyData s2 t):ts)

typeDataVariant env qmap (DataVariant c l tses) = let es = map snd tses in do
    (s, ts) <- typeTyExprsConcrete env qmap es
    return (s, DataVariant c l (zip ts es))

typeDataVariants env qmap [] = return (nullKSubst, [])
typeDataVariants env qmap (v:vs) = do
    (s, v') <- typeDataVariant env qmap v
    (s', vs') <- typeDataVariants env (substApplyQmap s qmap) vs
    return (composeKSubst s' s, (substApplyVariant s' v'):vs')
