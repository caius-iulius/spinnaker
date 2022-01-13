module SyntaxDefs where
import MPCL(StdCoord)
import TypingDefs
import HLDefs

data Path = Path [String] String
    deriving Show

type SyntaxPattern = HLPattern Path

type SyntaxExpr = HLExpr Path

-- TODO Rifai in vista dei tipi higher kinded
data SyntaxTypeExprData
    = TypeExprQuantifier String -- Nome del quantifier, forse va incorporato con TypeExprName?
    | TypeExprTuple [SyntaxTypeExpr] --Lista di tipi della n-tupla
    | TypeExprName Path -- Nome del tipo
    | TypeExprApp SyntaxTypeExpr SyntaxTypeExpr --Tipo funzione, tipo argomento
    deriving Show
type SyntaxTypeExpr = (StdCoord, SyntaxTypeExprData)

data SyntaxDataVariant =
    DataVariant StdCoord String [(DataType, SyntaxTypeExpr)] --Coordinate della definizione, nome della variante, lista di argomenti sia come tipo concreto (da assegnare in fase di tipizzazione), sia come espressione di tipi
    deriving Show

type SyntaxValDef = HLValDef Path

data SyntaxDataDef =
    DataDef StdCoord Visibility String [(String, TyQuant)] [SyntaxDataVariant] --Coordinate della definizione, nome del tipo, lista di tipi argomento e quantificatori corrispondenti (da assegnare in fase di tipizzazione), varianti del tipo
    deriving Show
type SyntaxDataDefGroup = [SyntaxDataDef]

data Visibility = Public | Private
    deriving Show

data SyntaxModDef
    = ModMod StdCoord Visibility String SyntaxModule
    | ModUse StdCoord Visibility Path
    | ModValGroup [(Visibility, SyntaxValDef)]
    | ModDataGroup SyntaxDataDefGroup
    deriving Show
data SyntaxModule = Module [SyntaxModDef]
    deriving Show
