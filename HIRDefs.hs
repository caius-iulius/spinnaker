module HIRDefs where
import MPCL(StdCoord)
import TypingDefs

data Literal
    = LitInteger Int
    | LitFloating Float
    deriving Show

data Path = Path [String] String
    deriving Show

--Pattern nell'HIR
data HLPatternData a
    = PatWildcard
    | PatLiteral Literal --Il literal rappresentato
    | PatTuple [HLPattern a] --Lista di elementi della n-tupla
    | PatVariant a [HLPattern a] --Nome della variante, lista di argomenti di questo
    deriving Show
type HLPattern a = (StdCoord, Maybe String, HLPatternData a) -- coordinate, eventuale assegnazione del valore (tipo haskell labl@pat) e pattern vero e proprio
type HIRPattern = HLPattern Path

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
type HIRExpr = HLExpr Path

-- TODO Rifai in vista dei tipi higher kinded
data HIRTypeExprData
    = TypeExprQuantifier String -- Nome del quantifier, forse va incorporato con TypeExprName?
    | TypeExprTuple [HIRTypeExpr] --Lista di tipi della n-tupla
    | TypeExprName Path -- Nome del tipo
    | TypeExprApp HIRTypeExpr HIRTypeExpr --Tipo funzione, tipo argomento
    deriving Show
type HIRTypeExpr = (StdCoord, HIRTypeExprData)

data HIRDataVariant =
    DataVariant StdCoord String [(DataType, HIRTypeExpr)] --Coordinate della definizione, nome della variante, lista di argomenti sia come tipo concreto (da assegnare in fase di tipizzazione), sia come espressione di tipi
    deriving Show

data HLValDef a = ValDef StdCoord String (HLExpr a) -- Cordinate della definizione, nome del valore, espressione
    deriving Show
type HIRValDef = HLValDef Path

data HIRDataDef =
    DataDef StdCoord Visibility String [(String, TyQuant)] [HIRDataVariant] --Coordinate della definizione, nome del tipo, lista di tipi argomento e quantificatori corrispondenti (da assegnare in fase di tipizzazione), varianti del tipo
    deriving Show
type HIRDataDefGroup = [HIRDataDef]

data Visibility = Public | Private
    deriving Show

data HIRModDef
    = ModMod StdCoord Visibility String HIRModule
    | ModUse StdCoord Visibility Path
    | ModValGroup [(Visibility, HIRValDef)]
    | ModDataGroup HIRDataDefGroup
    deriving Show
data HIRModule = Module [HIRModDef]
    deriving Show

data BlockProgram = BlockProgram [[HLValDef String]]
