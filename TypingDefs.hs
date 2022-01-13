module TypingDefs where
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as Map

type KindQuant = Int

data Kind
    = KindNOTHING --Kind temporaneo generato dal parser
    | KStar
    | KindQuant KindQuant --Questo l'ho tolto perché alla fine dell'inferenza tutti i kind liberi diventano *
    | KFun Kind Kind
    deriving Eq

instance Show Kind where
    show KindNOTHING = "NOTHING"
    show KStar = "*"
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
    | DataQuant TyQuant --Quantificatore
    -- | DataTuple [DataType] --Lista dei tipi interni alla n-tupla
    | DataTypeName String Kind -- Nome del tipo, kind del tipo
    | DataTypeApp DataType DataType --Funzione di tipi, argomento
    deriving Eq

-- TODO: Miglior debug per tipi tupla (o tipi-nome)
instance Show DataType where
    show DataNOTHING = "NOTHING"
    show (DataQuant q) = show q
    -- show (DataTuple types) = "(" ++ foldr ((++) . (++ ",")) "" (map show types) ++ ")"
    show (DataTypeName s k) = s++":"++show k
    show (DataTypeApp (DataTypeApp (DataTypeName "->#BI" _) a) r) = "(" ++ show a ++ "->" ++ show r ++ ")" --Caso speciale per le funzioni
    show (DataTypeApp f a) = "(" ++ show f ++ " " ++ show a ++ ")"

data TyScheme = TyScheme [TyQuant] DataType
instance Show TyScheme where
    show (TyScheme qs dt) = let showq (TyQuant q k) = " " ++ show q ++ ":" ++ show k in
        "forall" ++ foldl (++) "" (map showq qs) ++ "." ++ show dt

data VariantData = VariantData String [TyQuant] [DataType] DataType -- Nome della variante, quantificatori generici, argomenti, datatype di appartenenza
    deriving Show
-- contesto dei tipi (Types), specie (Kinds) e costruttori (Variants)
data TypingEnv = TypingEnv (Map.Map String TyScheme) (Map.Map String Kind) (Map.Map String VariantData) --NOTE: Il nome della variante qui è duplicato
    deriving Show

--Definizioni utili
buildTupKind len = foldr (\_ ret -> KFun KStar ret) KStar [1..len]
buildTupType ts =
    let len = length ts
        labl = "()" ++ show len
    in foldl DataTypeApp (DataTypeName labl $ buildTupKind len) ts

buildFunType a r =
    DataTypeApp (DataTypeApp (DataTypeName "->#BI" (KFun KStar (KFun KStar KStar))) a) r
intT = DataTypeName "Int#BI" KStar
fltT = DataTypeName "Flt#BI" KStar
boolT = DataTypeName "Bool#BI" KStar
charT = DataTypeName "Char#BI" KStar
listT t = DataTypeApp (DataTypeName "List#BI" (KFun KStar KStar)) t

-- Infrastruttura monadica
data TIState = TIState KindQuant TyQuantId
    deriving Show

type TyperState t = ExceptT String (StateT TIState IO) t

newTyQuant :: Kind -> TyperState TyQuant
newTyQuant k = do
    (TIState kq tq) <- get
    put $ TIState kq (tq+1)
    return $ TyQuant tq k

freshType k = do
    q <- newTyQuant k
    return $ DataQuant q

newKindQuant :: TyperState KindQuant
newKindQuant = do
    (TIState k t) <- get
    put $ TIState (k+1) t
    return k

freshKind :: TyperState Kind
freshKind = do
    q <- newKindQuant
    return $ KindQuant q

runTyperState :: TyperState t -> IO (Either String t, TIState)
runTyperState t =
    runStateT (runExceptT t) (TIState 0 0)
