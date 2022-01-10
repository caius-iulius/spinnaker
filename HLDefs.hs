module HLDefs where
import MPCL(StdCoord)
import TypingDefs

data Literal
    = LitInteger Int
    | LitFloating Float
    deriving Show

--Pattern nell'HL e HIR
data HLPatternData a
    = PatWildcard
    | PatLiteral Literal --Il literal rappresentato
    | PatTuple [HLPattern a] --Lista di elementi della n-tupla
    | PatVariant a [HLPattern a] --Nome della variante, lista di argomenti di questo
    deriving Show
type HLPattern a = (StdCoord, Maybe String, HLPatternData a) -- coordinate, eventuale assegnazione del valore (tipo haskell labl@pat) e pattern vero e proprio

data HLExprData a
    = ExprLiteral Literal --Valore letterale
    | ExprApp (HLExpr a) (HLExpr a) --Funzione, argomento
    | ExprLabel a --Riferimento a label
    | ExprConstructor a -- Riferimento a una variante
    | ExprTuple [(HLExpr a)] --Elementi della n-tupla
    | ExprLambda (HLPattern a) (HLExpr a) --Argomento(anche "smontato") e valore interno
    | ExprPut (HLExpr a) [(HLPattern a, HLExpr a)] --Valore da controllare, lista di pattern e i branch corrispondenti
    deriving Show
type HLExpr a = (StdCoord, DataType, HLExprData a)

data HLValDef a = ValDef StdCoord String (HLExpr a) -- Cordinate della definizione, nome del valore, espressione
    deriving Show

data BlockProgram = BlockProgram [[HLValDef String]]
