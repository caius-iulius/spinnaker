module SyntaxDefs where
import MPCL(StdCoord)
import TypingDefs
import HLDefs(Literal(..))

data Path = Path [String] String
    deriving Show

data SyntaxPatternData
    = SynPatWildcard
    | SynPatLiteral Literal --Il literal rappresentato
    | SynPatTuple [SyntaxPattern] --Lista di elementi della n-tupla
    | SynPatVariant Path [SyntaxPattern] --Nome della variante, lista di argomenti di questo
    deriving Show
type SyntaxPattern = (StdCoord, Maybe String, SyntaxPatternData) -- coordinate, eventuale assegnazione del valore (tipo haskell labl@pat) e pattern vero e proprio

data SyntaxExprData
    = SynExprLiteral Literal --Valore letterale
    | SynExprApp SyntaxExpr SyntaxExpr --Funzione, argomento
    | SynExprLabel Path --Riferimento a label
    | SynExprConstructor Path -- Riferimento a una variante
    | SynExprTuple [SyntaxExpr] --Elementi della n-tupla
    | SynExprLambda SyntaxPattern SyntaxExpr --Argomento(anche "smontato") e valore interno
    | SynExprPut SyntaxExpr [(SyntaxPattern, SyntaxExpr)] --Valore da controllare, lista di pattern e i branch corrispondenti
    deriving Show
type SyntaxExpr = (StdCoord, SyntaxExprData)

data SyntaxValDef = SynValDef StdCoord String (SyntaxExpr) -- Cordinate della definizione, nome del valore, espressione
    deriving Show

-- TODO Rifai in vista dei tipi higher kinded
data SyntaxTypeExprData
    = SynTypeExprQuantifier String -- Nome del quantifier, forse va incorporato con SynTypeExprName?
    | SynTypeExprTuple [SyntaxTypeExpr] --Lista di tipi della n-tupla
    | SynTypeExprName Path -- Nome del tipo
    | SynTypeExprApp SyntaxTypeExpr SyntaxTypeExpr --Tipo funzione, tipo argomento
    deriving Show
type SyntaxTypeExpr = (StdCoord, SyntaxTypeExprData)

data SyntaxDataVariant =
    DataVariant StdCoord String [(DataType, SyntaxTypeExpr)] --Coordinate della definizione, nome della variante, lista di argomenti sia come tipo concreto (da assegnare in fase di tipizzazione), sia come espressione di tipi
    deriving Show

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
