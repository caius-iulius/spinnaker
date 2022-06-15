module HLDefs where
import MPCL(StdCoord)
import TypingDefs

data Literal
    = LitInteger Int
    | LitFloating Float
    deriving (Show, Eq)

data HLPatternData
    = PatWildcard
    | PatLiteral Literal --Il literal rappresentato
    | PatVariant String [HLPattern] --Nome della variante, lista di argomenti di questo
    deriving Show
type HLPattern = (StdCoord, Maybe String, HLPatternData) -- coordinate, eventuale assegnazione del valore (tipo haskell labl@pat) e pattern vero e proprio

data HLExprData
    = ExprLiteral Literal --Valore letterale
    | ExprApp HLExpr HLExpr --Funzione, argomento
    | ExprLabel String --Riferimento a label
    | ExprConstructor String [HLExpr] -- Riferimento a una variante e argomenti "applicati"
    | ExprLambda HLPattern HLExpr --Argomento(anche "smontato") e valore interno
    | ExprPut HLExpr [(HLPattern, HLExpr)] --Valore da controllare, lista di pattern e i branch corrispondenti
    deriving Show
type HLExpr = (StdCoord, DataType, HLExprData)

data HLTypeExprData
    = TypeExprQuant TyQuant
    | TypeExprName String
    | TypeExprApp HLTypeExpr HLTypeExpr
    deriving Show
type HLTypeExpr = (StdCoord, HLTypeExprData)
type HLTySchemeExpr = HLTypeExpr

data HLValDef
    = ValDef StdCoord String (Maybe (HLTySchemeExpr, DataType)) HLExpr -- Cordinate della definizione, nome del valore, type hint, espressione
    deriving Show

data HLDataVariant
    = DataVariant StdCoord String [(HLTypeExpr, DataType)]
    deriving Show

data HLDataDef
    = DataDef StdCoord String [(String, TyQuant)] [HLDataVariant]
    deriving Show

data BlockProgram = BlockProgram [[HLDataDef]] [[HLValDef]]
