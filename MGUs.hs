module MGUs where
import Control.Monad.Trans
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe(isJust, isNothing, catMaybes)
import MPCL(StdCoord, dummyStdCoord)
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

    freeKindQuants KType = Set.empty
    freeKindQuants (KindQuant q) = Set.singleton q
    freeKindQuants (KFun k k') = Set.union (freeKindQuants k) (freeKindQuants k')


instance Kinds TyQuant where
    kind (TyQuant _ k) = k
    kSubstApply s (TyQuant t k) = TyQuant t (kSubstApply s k)
    freeKindQuants (TyQuant _ k) = freeKindQuants k

instance Kinds DataType where
    kind (DataQuant q) = kind q
    --kind (DataTuple _) = KType
    kind (DataTypeName _ k) = k
    kind (DataTypeApp t _) = let (KFun _ k) = kind t in k
    kind (DataCOORD _ t) = kind t

    kSubstApply s (DataQuant q) = DataQuant (kSubstApply s q)
    --kSubstApply s (DataTuple ts) = DataTuple (map (kSubstApply s) ts)
    kSubstApply s (DataTypeName l k) = DataTypeName l (kSubstApply s k)
    kSubstApply s (DataTypeApp t1 t2) = DataTypeApp (kSubstApply s t1) (kSubstApply s t2)
    kSubstApply s (DataCOORD c t) = DataCOORD c (kSubstApply s t)

    freeKindQuants (DataQuant q) = freeKindQuants q
    freeKindQuants (DataTypeName _ k) = freeKindQuants k
    freeKindQuants (DataTypeApp f a) = Set.union (freeKindQuants f) (freeKindQuants a)
    freeKindQuants (DataCOORD _ t) = freeKindQuants t

substApplyPred s (Pred l ts) = Pred l $ map (kSubstApply s) ts
freeKindQuantsPred (Pred l ts) = Set.unions (map freeKindQuants ts)
instance Kinds t => Kinds (Qual t) where
    kind (Qual _ t) = kind t
    kSubstApply s (Qual ps t) = Qual (map (substApplyPred s) ps) (kSubstApply s t)
    freeKindQuants (Qual ps t) = Set.unions (freeKindQuants t : map freeKindQuantsPred ps)

nullKSubst :: KindSubst
nullKSubst = Map.empty

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
    freetyvars (DataCOORD _ t) = freetyvars t

    substApply s (DataQuant q) = case Map.lookup q s of
        Nothing -> DataQuant q
        Just t -> t
    substApply s (DataTypeApp dta dtb) =
        DataTypeApp (substApply s dta) (substApply s dtb)
    substApply s (DataTypeName tn k) = DataTypeName tn k
    --substApply s t = error $ "APPLY: " ++ show s ++ show t
    substApply s (DataCOORD c t) = DataCOORD c (substApply s t)

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


--TODO: Sposta in altro file, sono funzioni per l'env
--tyBindRemove (TypingEnv typeEnv kindEnv) labl = TypingEnv (Map.delete labl typeEnv) kindEnv
tyBindAdd :: StdCoord -> TypingEnv -> String -> TyScheme -> TypingEnv
tyBindAdd c (TypingEnv ts ks vs rs) labl scheme =
    case Map.lookup labl ts of
        --Just _ -> fail $ show c ++ " Variable already bound: " ++ labl
        Nothing -> --do
            --lift $ lift $ putStrLn $ show c ++ " Binding variable: " ++ labl ++ ":" ++ show scheme
            --return $
            TypingEnv (Map.insert labl scheme ts) ks vs rs

generalize :: TypingEnv -> Qual DataType -> TyScheme
generalize env t =
    let quants = Set.toList $ Set.difference (freetyvars t) (freetyvars env)
    in TyScheme quants t

getInstantiationSubst qs = do
    nqs <- mapM (\(TyQuant _ k) -> freshType k) qs
    return $ Map.fromList (zip qs nqs)

instantiate :: TyScheme -> TyperState (Qual DataType)
instantiate scm@(TyScheme qs t) = do
    subst <- getInstantiationSubst qs
    lift $ lift $ putStrLn $ "Instantiating: " ++ show scm ++ " with subst: " ++ show subst
    return $ substApply subst t

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
match :: MonadFail m => StdCoord -> DataType -> DataType -> m Subst
match c src tgt = do
    s <- mgu c src tgt
    let
        keyss = Set.fromList $ map fst $ Map.toList s
        frees = freetyvars tgt
        transformsInTgt = Set.intersection keyss frees
        in if length transformsInTgt /= 0
        then fail $ show c ++ " Could not match type: " ++ show src ++ " into: " ++ show tgt
        else return s

liftUnionPred m c (Pred l ts) (Pred l' ts')
    | l == l' = liftUnionList m c (zip ts ts')
    | otherwise = fail $ show c ++ " Rel labels differ: " ++ l ++ " and " ++ l'

mguPred, matchPred :: Pred -> Pred -> Maybe Subst
mguPred = liftUnionPred mgu dummyStdCoord
matchPred = liftUnionPred match dummyStdCoord

data ChooseInstRes --TODO: Questa interfaccia non è corretta
    = OneMatch [Pred]
    | MultipleMatches [InstData]
    | NoUnifiers
    | PossibleUnifiers [InstData]
    deriving Show

insts :: TypingEnv -> String -> [InstData]
insts (TypingEnv _ _ _ rels) l =
    case Map.lookup l rels of
        Just (RelData _ _ _ idatas) -> idatas

supers :: TypingEnv -> Pred -> [Pred]
supers (TypingEnv _ _ _ rels) (Pred l ts) =
    case Map.lookup l rels of
        Just (RelData qs ps _ _) ->
            let s = Map.fromList (zip qs ts) in
                map (substApply s) ps

bySuper :: TypingEnv -> Pred -> [Pred]
bySuper env p = p:concat [bySuper env p' | p' <- supers env p]

chooseInst :: TypingEnv -> Pred -> ChooseInstRes
chooseInst env p@(Pred l ts) =
    let matchInsts = getBestUniInsts matchPred
        mguInsts = getBestUniInsts mguPred
        in if length mguInsts == 0 then NoUnifiers
        else case matchInsts of
            [] -> PossibleUnifiers mguInsts --No matching instances, failure?
            (i@(Qual ps h):[]) -> --Se è l'unica instance specifica
                if elem i mguInsts then case matchPred h p of--Se è tra i più specifici di tutte le possibili instances
                    --TODO: elem controlla tutto il predicato qualificato, forse dovrebbe ignorare i qualificatori
                    Just u -> OneMatch (map (substApply u) ps) --Allora prendi i constraint
                else PossibleUnifiers mguInsts --altrimenti niente, i constraint potrebbero cambiare con un tipo più specifico
            ps -> MultipleMatches ps --Ci sono più instance specifiche
    where
        reduceToSpecifics :: [Qual Pred] -> [Qual Pred] -> [Qual Pred]
        reduceToSpecifics sqs [] = sqs
        reduceToSpecifics sqs (q@(Qual _ h):qs) =
            let areThereMoreSpecific = any (\(Qual _ h') ->
                        isJust (matchPred h h') && isNothing (matchPred h' h)
                    ) (sqs ++ qs)
                in case areThereMoreSpecific of
                    True -> reduceToSpecifics sqs qs
                    False -> reduceToSpecifics (q:sqs) qs
        tryInstUnion m q@(Qual _ h) = do
            u <- m h p
            Just q
        getBestUniInsts m  =
            let uniInsts = catMaybes [tryInstUnion m it | it <- insts env l]
                in reduceToSpecifics [] uniInsts

entail :: TypingEnv -> [Pred] -> Pred -> Bool
entail env ps p
    = any (elem p) (map (bySuper env) ps)
    || case chooseInst env p of
        OneMatch qs -> all (entail env ps) qs
        _ -> False

entailInsts :: TypingEnv -> [Pred] -> Pred -> Bool
entailInsts env ps p
    = elem p ps
    || case chooseInst env p of
        OneMatch qs -> all (entailInsts env ps) qs -- forse dovrei usare entail
        _ -> False

simplify env = loop []
    where
        loop sps [] = sps
        loop sps (p:ps) | entail env (sps ++ ps) p = loop sps ps
                        | otherwise = loop (p:sps) ps

toHnfs :: MonadFail m => StdCoord -> TypingEnv -> [Pred] -> m [Pred]
toHnfs c env ps = do
        pss <- mapM (toHnf c env) ps
        return (concat pss)
toHnf :: MonadFail m => StdCoord -> TypingEnv -> Pred -> m [Pred]
toHnf c env p = case chooseInst env p of
    OneMatch ps -> toHnfs c env ps
    NoUnifiers -> fail $ show c ++ " No compatible instance for: " ++ show p ++ "\n    Instances for rel: " ++ show (insts env $ (\(Pred l _)->l) p)
    _ -> return [p] -- TODO: In certi casi anche qui serve un fail (quando per esempio è sicuramente impossibile decidere l'instance più specifica)--TODO: forse bisogna usare la regola isHnf
reduce :: MonadFail m => StdCoord -> TypingEnv -> [Pred] -> m [Pred]
reduce c env ps = do
    qs <- toHnfs c env ps
    return (simplify env qs)

--TODO: Questa funzione tiene in conto anche delle variabili libere nell'env, dovrebbe essere la cosa giusta ma non ne sono del tutto sicuro
checkAmbiguousQual :: (Types t, Show t) => StdCoord -> TypingEnv -> Qual t -> TyperState ()
checkAmbiguousQual c env (Qual ps t) =
    let freepsvars = Set.unions $ map freetyvars ps
        freedatavars = Set.union (freetyvars t) (freetyvars env)
        difference = Set.difference freepsvars freedatavars
        in if length difference == 0 then return ()
        else fail $ show c ++ " Qualifier is ambiguous, it qualifies over type variables: " ++ show (Set.toList difference) ++ " in: " ++ show (Qual ps t)
