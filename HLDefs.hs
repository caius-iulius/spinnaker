module HLDefs where
import MPCL(StdCoord)
import TypingDefs

data Literal
    = LitInteger Int
    | LitFloating Float
    deriving Show

data HLPatternData
    = PatWildcard
    | PatLiteral Literal --Il literal rappresentato
    -- | PatTuple [HLPattern a] --Lista di elementi della n-tupla
    | PatVariant String [HLPattern] --Nome della variante, lista di argomenti di questo
    deriving Show
type HLPattern = (StdCoord, Maybe String, HLPatternData) -- coordinate, eventuale assegnazione del valore (tipo haskell labl@pat) e pattern vero e proprio

data HLExprData
    = ExprLiteral Literal --Valore letterale
    | ExprApp HLExpr HLExpr --Funzione, argomento
    | ExprLabel String --Riferimento a label
    | ExprConstructor String -- Riferimento a una variante
    -- | ExprTuple [(HLExpr a)] --Elementi della n-tupla
    | ExprLambda HLPattern HLExpr --Argomento(anche "smontato") e valore interno
    | ExprPut HLExpr [(HLPattern, HLExpr)] --Valore da controllare, lista di pattern e i branch corrispondenti
    deriving Show
type HLExpr = (StdCoord, DataType, HLExprData)

data HLValDef = ValDef StdCoord String HLExpr -- Cordinate della definizione, nome del valore, espressione
    deriving Show

data BlockProgram = BlockProgram [[HLValDef]]
