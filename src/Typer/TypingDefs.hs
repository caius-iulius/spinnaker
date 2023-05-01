module Typer.TypingDefs where
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set

import CompDefs
import ResultT
import Parser.MPCL(StdCoord)

type KindQuant = Int

data Kind
    = KindNOTHING --Kind temporaneo generato dal parser
    | KType
    | KindQuant KindQuant --Questo l'ho tolto perché alla fine dell'inferenza tutti i kind liberi diventano *
    | KFun Kind Kind
    deriving Eq

data DataType
    = DataNOTHING --Tipo temporaneo generato dal parser
    | DataCOORD StdCoord DataType --Tipo temporaneo generato dal parser, serve per migliorare i messaggi di errore nel kind inference, dopodiché vengono eliminati.
    | DataQuant TyQuant --Quantificatore
    | DataTypeName String Kind -- Nome del tipo, kind del tipo
    | DataTypeApp DataType DataType --Funzione di tipi, argomento

type KindSubst = Map.Map KindQuant Kind
-- Classe kinds, usata per sostituzioni e per avere il kind
class Kinds t where
    kind :: t->Kind
    kSubstApply :: KindSubst -> t -> t
    freeKindQuants :: t -> Set.Set KindQuant

type Subst = Map.Map TyQuant DataType
class Types t where
    freetyvars :: t -> Set.Set TyQuant
    substApply :: Subst -> t -> t


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

substApplyPred :: KindSubst -> Pred -> Pred
substApplyPred s (Pred l ts) = Pred l $ map (kSubstApply s) ts

freeKindQuantsPred :: Pred -> Set.Set KindQuant
freeKindQuantsPred (Pred l ts) = Set.unions (map freeKindQuants ts)

instance Kinds t => Kinds (Qual t) where
    kind (Qual _ t) = kind t
    kSubstApply s (Qual ps t) = Qual (map (substApplyPred s) ps) (kSubstApply s t)
    freeKindQuants (Qual ps t) = Set.unions (freeKindQuants t : map freeKindQuantsPred ps)

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
    freetyvars (Qual ps t) = Set.unions $ freetyvars t : map freetyvars ps
    substApply s (Qual ps t) = Qual (map (substApply s) ps) (substApply s t)

instance Types TyScheme where
    freetyvars (TyScheme qs dt) = Set.difference (freetyvars dt) (Set.fromList qs)
    substApply s (TyScheme qs dt) = TyScheme qs (substApply (foldr Map.delete s qs) dt)

instance Types TypingEnv where
    freetyvars (TypingEnv ts _ _ _ _) = Set.unions $ map freetyvars (Map.elems ts)
    substApply s (TypingEnv ts ks vs cs rs) = TypingEnv (Map.map (substApply s) ts) ks vs cs rs

instance Show Kind where
    show KindNOTHING = "NOTHING"
    show KType = "T"
    show (KindQuant q) = "k" ++ show q
    show (KFun a r) = "(" ++ show a ++ "->" ++ show r ++ ")"

type TyQuantId = Int
data TyQuant = TyQuant TyQuantId Kind
    deriving Eq
instance Ord TyQuant where
    compare (TyQuant t1 _) (TyQuant t2 _) = compare t1 t2
instance Show TyQuant where
    show (TyQuant i k) = "q"++show i++":"++show k

instance Eq DataType where
    DataCOORD _ t == t' = t == t'
    t == DataCOORD _ t' = t == t'
    DataQuant q == DataQuant q' = q == q'
    DataTypeName l k == DataTypeName l' k' = l == l' && k == k'
    DataTypeApp f a == DataTypeApp f' a' = f == f' && a == a'
    _ == _ = False

-- TODO: Miglior debug per tipi tupla (o tipi-nome)
instance Show DataType where
    show DataNOTHING = "NOTHING"
    show (DataCOORD c dt) = "(AT"++show c ++ " " ++ show dt ++ ")"
    show (DataQuant q) = show q
    show (DataTypeName s k) = s++":"++show k
    show (DataTypeApp (DataTypeApp (DataTypeName "->#BI" _) a) r) = "(" ++ show a ++ "->" ++ show r ++ ")" --Caso speciale per le funzioni
    show (DataTypeApp f a) = "(" ++ show f ++ " " ++ show a ++ ")"

data Pred = Pred String [DataType]
    deriving Eq
instance Show Pred where
    show (Pred l ts) = l ++ concatMap ((' ':) . show) ts

data Qual t = Qual [Pred] t
    deriving Eq

instance Show t => Show (Qual t) where
    show (Qual ps a) = '{': foldr (\l r->show l ++ ", " ++ r) "} => " ps ++ show a

data TyScheme = TyScheme [TyQuant] (Qual DataType)
instance Show TyScheme where
    show (TyScheme qs dt) = let showq (TyQuant q k) = " " ++ show q ++ ":" ++ show k in
        "forall" ++ concatMap showq qs ++ "." ++ show dt

data VariantData = VariantData String [TyQuant] [DataType] DataType -- Nome della variante, quantificatori generici, argomenti, datatype di appartenenza
    deriving Show

type CombData = ([DataType], DataType)
-- Definizioni rel
type InstData = Qual Pred
data RelData = RelData [TyQuant] [Pred] [(String, Qual DataType)] [InstData]
    deriving Show
type RelEnv = Map.Map String RelData

-- contesto dei tipi (Types), specie (Kinds), costruttori (Variants), combinatori e relazioni
data TypingEnv = TypingEnv (Map.Map String TyScheme) (Map.Map String Kind) (Map.Map String VariantData) (Map.Map String CombData) RelEnv --NOTE: Il nome della variante qui è duplicato
    deriving Show

--Definizioni utili
isTupLabl :: String -> (Bool, Int) --TODO: usa un maybe
isTupLabl "()" = (True, 0)
isTupLabl ('(':rest) = (")" == dropWhile (','==) rest, length rest)
isTupLabl _ = (False, 0)

makeTupLabl :: Int -> String
makeTupLabl 0 = "()"
makeTupLabl 1 = error "Tuples of length 1 are forbidden"
makeTupLabl len = '(':replicate (len - 1) ',' ++")"

buildTupKind :: Int -> Kind
buildTupKind len = foldr (\_ ret -> KFun KType ret) KType [1..len]

buildTupType :: [DataType] -> DataType
buildTupType ts =
    let len = length ts
        labl = makeTupLabl len
    in foldl DataTypeApp (DataTypeName labl $ buildTupKind len) ts

buildFunType :: DataType -> DataType -> DataType
buildFunType a r =
    DataTypeApp (DataTypeApp (DataTypeName "->#BI" (KFun KType (KFun KType KType))) a) r

intT, fltT, boolT, chrT, realworldT :: DataType
intT = DataTypeName "Int#BI" KType
fltT = DataTypeName "Flt#BI" KType
boolT = DataTypeName "Bool#BI" KType
chrT = DataTypeName "Chr#BI" KType
realworldT = DataTypeName "RealWorld_#BI" KType

-- Infrastruttura monadica

type TyperStateData = (Int, KindQuant, TyQuantId)

type TyperState t = ResultT (StateT TyperStateData CompMon) t

typerLog :: String -> TyperState ()
typerLog = lift . lift . compLog

newUniqueSuffix :: TyperState String
newUniqueSuffix = do
    (u, k, t) <- get
    put (u+1, k, t)
    return ('#':show u)

newTyQuant :: Kind -> TyperState TyQuant
newTyQuant k = do
    (u, kq, tq) <- get
    put (u, kq, tq+1)
    return $ TyQuant tq k

freshType :: Kind -> TyperState DataType
freshType k = do
    q <- newTyQuant k
    return $ DataQuant q

newKindQuant :: TyperState KindQuant
newKindQuant = do
    (u, k, t) <- get
    put (u, k+1, t)
    return k

freshKind :: TyperState Kind
freshKind = KindQuant <$> newKindQuant

dataQsToKind :: [(String, TyQuant)] -> Kind
dataQsToKind = foldr (KFun . kind . snd) KType

runTyperState :: TyperStateData -> TyperState t -> CompMon (Either String t, TyperStateData)
runTyperState s t =
    runStateT (runResultT t) s
