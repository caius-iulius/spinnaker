module HLDefs where
import MPCL(StdCoord)
import TypingDefs

data Literal
    = LitInteger Int
    | LitFloating Float
    | LitCharacter Char
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
    | ExprCombinator String [HLExpr] -- Riferimento al combinatore e argomenti
    | ExprLambda HLPattern HLExpr --Argomento(anche "smontato") e valore interno
    | ExprPut HLExpr [(HLPattern, HLExpr)] --Valore da controllare, lista di pattern e i branch corrispondenti
    | ExprHint DataType HLExpr --type hint di un'espressione
    deriving Show
type HLExpr = (StdCoord, DataType, HLExprData)

data HLValDef
    = ValDef StdCoord String (Maybe (Qual DataType)) [Pred] HLExpr -- Cordinate della definizione, nome del valore, type hint, espressione
    deriving Show

data HLExtDef = ExtDef StdCoord String [DataType] DataType
    deriving Show

data HLDataVariant
    = DataVariant StdCoord String [(StdCoord, DataType)]
    deriving Show

data HLDataDef
    = DataDef StdCoord String [(String, TyQuant)] [HLDataVariant]
    deriving Show

data HLRelDef
    = RelDef StdCoord String [TyQuant] [Pred] [(StdCoord, String, Qual DataType)]
    deriving Show

data HLInstDef
    = InstDef StdCoord (Qual Pred) [(StdCoord, String, HLExpr)]
    deriving Show

data BlockProgram = BlockProgram [[HLDataDef]] [HLRelDef] [HLExtDef] [[HLValDef]] [HLInstDef]
