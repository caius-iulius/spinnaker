module TypingDefs where
import Control.Monad.Except
import Control.Monad.State

type KindQuant = Int

data Kind
    = KindNOTHING --Kind temporaneo generato dal parser
    | KindConcrete
    | KindQuant KindQuant --Questo l'ho tolto perché alla fine dell'inferenza tutti i kind liberi diventano *
    | KindFunction Kind Kind
    deriving Eq

instance Show Kind where
    show KindNOTHING = "NOTHING"
    show KindConcrete = "*"
    show (KindQuant q) = "k" ++ show q
    show (KindFunction a r) = "(" ++ show a ++ "->" ++ show r ++ ")"


type TyQuant = Int

data DataType
    = DataNOTHING --Tipo temporaneo generato dal parser
    -- | DataInt
    -- | DataFlt
    | DataQuant TyQuant --Quantificatore
    | DataTuple [DataType] --Lista dei tipi interni alla n-tupla
    | DataTypeName String -- Nome del tipo
    | DataTypeApp DataType DataType --Funzione di tipi, argomento
    deriving Eq

instance Show DataType where
    show DataNOTHING = "NOTHING"
    -- show DataInt = "Int"
    -- show DataFlt = "Flt"
    show (DataQuant q) = "q"++ show q
    show (DataTuple types) = "(" ++ foldr ((++) . (++ ",")) "" (map show types) ++ ")"
    --show (DataFun a r) = "(" ++ show a ++ "->" ++ show r ++ ")"
    --show (DataTypeApp s types) = "(" ++ foldr1 ((++) . (++ " ")) (s:map show types) ++ ")"
    show (DataTypeName s) = s
    show (DataTypeApp (DataTypeApp (DataTypeName "->") a) r) = "(" ++ show a ++ "->" ++ show r ++ ")" --Caso speciale per le funzioni
    show (DataTypeApp f a) = "(" ++ show f ++ " " ++ show a ++ ")"


-- Infrastruttura monadica
data TIState = TIState KindQuant TyQuant
    deriving Show

type TyperState t = ExceptT String (StateT TIState IO) t

newTyQuant :: TyperState TyQuant
newTyQuant = do
    (TIState k t) <- get
    put $ TIState k (t+1)
    return t

freshType = do
    q <- newTyQuant
    return $ DataQuant q

newKindQuant :: TyperState KindQuant
newKindQuant = do
    (TIState k t) <- get
    put $ TIState (k+1) t
    return k

runTyperState :: TyperState t -> IO (Either String t, TIState)
runTyperState t =
    runStateT (runExceptT t) (TIState 0 0)
