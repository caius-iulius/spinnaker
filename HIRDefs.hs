module HIRDefs where
import MPCL(StdCoord)
import TypingDefs
import HLDefs

data Path = Path [String] String
    deriving Show

type HIRPattern = HLPattern Path

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
