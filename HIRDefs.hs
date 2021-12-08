module HIRDefs where
import MPCL(StdCoord)

type TyQuant = Int

--TODO DataType...
data DataType
    = DataNOTHING --Tipo temporaneo generato dal parser
    | DataInt
    | DataFlt
    | DataTuple [DataType] --Lista dei tipi interni alla n-tupla
    | DataFun DataType DataType --Tipo dell'argomento e del valore restituito
    | DataQuant TyQuant --Quantificatore
    | DataTypeApp String [DataType] --Nome del tipo, lista dei suoi argomenti

instance Show DataType where
    show DataNOTHING = "NOTHING"
    show DataInt = "Int"
    show DataFlt = "Flt"
    show (DataTuple types) = "(" ++ foldr ((++) . (++ ",")) "" (map show types) ++ ")"
    show (DataFun a r) = "(" ++ show a ++ "->" ++ show r ++ ")"
    show (DataQuant q) = "q"++ show q
    show (DataTypeApp s types) = "(" ++ foldr1 ((++) . (++ " ")) (s:map show types) ++ ")"

data Literal
    = LitInteger Int
    | LitFloating Float
    deriving Show

--Pattern nell'HIR
data HIRPatternData
    = PatWildcard
    | PatLiteral Literal --Il literal rappresentato
    | PatLabel String --Assegnazione valore a label
    | PatTuple [HIRPattern] --Lista di elementi della n-tupla
    | PatVariant String [HIRPattern] --Nome della variante, lista di argomenti di questo
    deriving Show
type HIRPattern = (StdCoord, HIRPatternData)


data HIRExprData 
    = ExprLiteral Literal --Valore letterale
    | ExprFCall HIRExpr HIRExpr --Funzione, argomento
    | ExprLabel String --Riferimento a label
    | ExprTuple [HIRExpr] --Elementi della n-tupla
    | ExprLambda HIRPattern HIRExpr --Argomento(anche "smontato") e valore interno
    | ExprPut HIRExpr [(HIRPattern, HIRExpr)] --Valore da controllare, lista di pattern e i branch corrispondenti
    deriving Show
type HIRExpr = (StdCoord, HIRExprData)

data HIRTypeExprData
    = TypeExprFun HIRTypeExpr HIRTypeExpr --Tipo argomento, tipo restituito
    | TypeExprTuple [HIRTypeExpr] --Lista di tipi della n-tupla
    | TypeExprTypeApp String [HIRTypeExpr] --Nome del tipo, argomenti del tipo
    | TypeExprQuantifier String --Nome del singolo valore...TODO migliore documentazione
    deriving Show
type HIRTypeExpr = (StdCoord, HIRTypeExprData)

data HIRDataVariant =
    DataVariant StdCoord String [(DataType, HIRTypeExpr)] --Coordinate della definizione, nome della variante, lista di argomenti sia come tipo concreto (da assegnare in fase di tipizzazione), sia come espressione di tipi
    deriving Show

data HIRDataDef =
    DataDef String [(TyQuant, String)] [HIRDataVariant] --Nome del tipo, lista di tipi argomento e quantificatori corrispondenti (da assegnare in fase di tipizzazione), varianti del tipo
    deriving Show

data HIRProgramDefs
    = ProgDefs [(StdCoord, String, HIRExpr)] --Lista di coordinate, nome e valore della definizione
    | ProgDataDefs [(StdCoord, HIRDataDef)] --Lista di coordinate e definizioni di tipo
    deriving Show
