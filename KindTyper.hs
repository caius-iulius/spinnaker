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

substApplyKindEnv s (TypingEnv ts ks vs) = TypingEnv ts (Map.map (substApplyKind s) ks) vs

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
typeTyExpr :: TypingEnv -> Map.Map String (TyQuant, Kind) -> HIRTypeExpr -> TyperState (KindSubst, Kind, DataType)
typeTyExpr _ qmap (c, TypeExprQuantifier l) =
    case Map.lookup l qmap of
        Nothing -> throwError $ show c ++ " Unbound quantifier: " ++ l
        Just (q, k) -> return (nullKSubst, k, DataQuant q)
typeTyExpr env qmap (c, TypeExprTuple exprs) = error "TODO"
typeTyExpr (TypingEnv _ env _) _ (c, TypeExprName l) =
    case Map.lookup l env of
        Nothing -> throwError $ show c ++ " Unbound type name: " ++ l
        Just k -> return (nullKSubst, k, DataTypeName l)
typeTyExpr env qmap (c, TypeExprApp f a) = do
    q <- freshKind
    (s1, k1, tf) <- typeTyExpr env qmap f
    (s2, k2, ta) <- typeTyExpr (substApplyKindEnv s1 env) qmap a
    s3 <- kindmgu c (substApplyKind s2 k1) (KindFunction k2 q)
    let finals = composeKSubst s3 (composeKSubst s2 s1) in
        let finalk = substApplyKind s3 q in
            return (finals, finalk, DataTypeApp tf ta)
    
{-
typeDataDef :: TypingEnv -> HIRDataDef -> TyperState (KindSubst, TypingEnv, [HIRDataDef])
typeDataDef env (DataDef c labl qsls variants) = do
    qsls' <- mapM (\(_, l)->do{newq <- freshKind; return (newq, l)}) qsls
    mykind <- return $ foldr (\(k, _) next->KindFunction k next) KindConcrete qsls'
-}
--typeDataDefs :: TypingEnv -> [HIRDataDef] -> TyperState (KindSubst, TypingEnv, [HIRDataDef])
