module HIRDefs where
import MPCL(StdCoord)
import TypingDefs

data Literal
    = LitInteger Int
    | LitFloating Float
    deriving Show

--Pattern nell'HIR
data HIRPatternData
    = PatWildcard
    | PatLiteral Literal --Il literal rappresentato
    | PatTuple [HIRPattern] --Lista di elementi della n-tupla
    | PatVariant String [HIRPattern] --Nome della variante, lista di argomenti di questo
    deriving Show
type HIRPattern = (StdCoord, Maybe String, HIRPatternData) -- coordinate, eventuale assegnazione del valore (tipo haskell labl@pat) e pattern vero e proprio


data HIRExprData 
    = ExprLiteral Literal --Valore letterale
    | ExprFCall HIRExpr HIRExpr --Funzione, argomento
    | ExprLabel String --Riferimento a label
    | ExprTuple [HIRExpr] --Elementi della n-tupla
    | ExprLambda HIRPattern HIRExpr --Argomento(anche "smontato") e valore interno
    | ExprPut HIRExpr [(HIRPattern, HIRExpr)] --Valore da controllare, lista di pattern e i branch corrispondenti
    deriving Show
type HIRExpr = (StdCoord, DataType, HIRExprData)

-- TODO Rifai in vista dei tipi higher kinded
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

data HIRValDef = ValDef StdCoord String HIRExpr -- Cordinate della definizione, nome del valore, espressione
    deriving Show
type HIRValDefs = [HIRValDef]

data HIRDataDef =
    DataDef StdCoord String [(TyQuant, String)] [HIRDataVariant] --Coordinate della definizione, nome del tipo, lista di tipi argomento e quantificatori corrispondenti (da assegnare in fase di tipizzazione), varianti del tipo
    deriving Show

data HIRProgram = Program [HIRDataDef] [HIRValDefs]
    deriving Show
