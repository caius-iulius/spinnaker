module TypingDefs where
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import ResultT
import MPCL(StdCoord)

type KindQuant = Int

data Kind
    = KindNOTHING --Kind temporaneo generato dal parser
    | KType
    | KindQuant KindQuant --Questo l'ho tolto perché alla fine dell'inferenza tutti i kind liberi diventano *
    | KFun Kind Kind
    deriving Eq

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

data DataType
    = DataNOTHING --Tipo temporaneo generato dal parser
    | DataCOORD StdCoord DataType --Tipo temporaneo generato dal parser, serve per migliorare i messaggi di errore nel kind inference, dopodiché vengono eliminati.
    | DataQuant TyQuant --Quantificatore
    | DataTypeName String Kind -- Nome del tipo, kind del tipo
    | DataTypeApp DataType DataType --Funzione di tipi, argomento

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
    show (Pred l ts) = l ++ (foldr (++) [] . map ((' ':) . show)) ts

data Qual t = Qual [Pred] t
    deriving Eq

instance Show t => Show (Qual t) where
    show (Qual ps a) = '{': (foldr (\l r->l ++ ", " ++ r) "} => " (map show ps)) ++ show a

data TyScheme = TyScheme [TyQuant] (Qual DataType)
instance Show TyScheme where
    show (TyScheme qs dt) = let showq (TyQuant q k) = " " ++ show q ++ ":" ++ show k in
        "forall" ++ foldl (++) "" (map showq qs) ++ "." ++ show dt

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
isTupLabl ('(':rest) = (")" == (dropWhile (','==) rest), length rest)
isTupLabl _ = (False, 0)

makeTupLabl 0 = "()"
makeTupLabl 1 = error "Tuples of length 1 are forbidden"
makeTupLabl len = '(':take (len - 1) (repeat ',')++")"

buildTupKind len = foldr (\_ ret -> KFun KType ret) KType [1..len]
buildTupType ts =
    let len = length ts
        labl = makeTupLabl len
    in foldl DataTypeApp (DataTypeName labl $ buildTupKind len) ts

buildFunType a r =
    DataTypeApp (DataTypeApp (DataTypeName "->#BI" (KFun KType (KFun KType KType))) a) r
intT = DataTypeName "Int#BI" KType
fltT = DataTypeName "Flt#BI" KType
boolT = DataTypeName "Bool#BI" KType
chrT = DataTypeName "Chr#BI" KType
realworldT = DataTypeName "RealWorld_#BI" KType

-- Infrastruttura monadica

type TyperStateData = (Int, KindQuant, TyQuantId)

type TyperState t = ResultT (StateT TyperStateData IO) t

compLog :: String -> IO ()
compLog = putStrLn
--compLog = const (return ())

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
    put (u, kq, (tq+1))
    return $ TyQuant tq k

freshType k = do
    q <- newTyQuant k
    return $ DataQuant q

newKindQuant :: TyperState KindQuant
newKindQuant = do
    (u, k, t) <- get
    put (u, (k+1), t)
    return k

freshKind :: TyperState Kind
freshKind = do
    q <- newKindQuant
    return $ KindQuant q

runTyperState :: TyperStateData -> TyperState t -> IO (Either String t, TyperStateData)
runTyperState state t =
    runStateT (runResultT t) state
