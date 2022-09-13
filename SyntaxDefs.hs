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
    | SynPatListNil -- lista vuota
    | SynPatListConss [SyntaxPattern] SyntaxPattern -- primi elementi della lista, continuazione
    deriving Show
type SyntaxPattern = (StdCoord, Maybe String, SyntaxPatternData) -- coordinate, eventuale assegnazione del valore (tipo haskell labl@pat) e pattern vero e proprio

data SyntaxExprData
    = SynExprLiteral Literal --Valore letterale
    | SynExprApp SyntaxExpr SyntaxExpr --Funzione, argomento
    | SynExprLabel Path --Riferimento a label
    | SynExprConstructor Path -- Riferimento a una variante
    | SynExprSndSection Path SyntaxExpr -- Sezioni di tipo (OP META)
    | SynExprTuple [SyntaxExpr] --Elementi della n-tupla
    | SynExprLambda [SyntaxPattern] SyntaxExpr --Argomento(anche "smontato") e valore interno
    | SynExprPut [SyntaxExpr] [([SyntaxPattern], SyntaxExpr)] --Valore da controllare, lista di pattern e i branch corrispondenti
    | SynExprString String -- Costante stringa
    | SynExprListNil -- lista vuota
    | SynExprListConss [SyntaxExpr] SyntaxExpr -- primi elementi della lista, continuazione
    | SynExprIfThenElse SyntaxExpr SyntaxExpr SyntaxExpr -- condizione, branch per true, branch per false
    | SynExprInlineUse Path SyntaxExpr -- modulo da portare nel contesto, espressione
    | SynExprBind SyntaxPattern SyntaxExpr SyntaxExpr --assegnazione, monade, funzione di trasformazione
    | SynExprHint SyntaxTypeExpr SyntaxExpr --type hint di un'espressione
    deriving Show
type SyntaxExpr = (StdCoord, SyntaxExprData)

data SyntaxTypeExprData
    = SynTypeExprQuantifier String -- Nome del quantifier, forse va incorporato con SynTypeExprName?
    | SynTypeExprTuple [SyntaxTypeExpr] --Lista di tipi della n-tupla
    | SynTypeExprName Path -- Nome del tipo
    | SynTypeExprApp SyntaxTypeExpr [SyntaxTypeExpr] --Tipo funzione, tipi argomento
    deriving Show
type SyntaxTypeExpr = (StdCoord, SyntaxTypeExprData)
type SyntaxTyPred = (StdCoord, Path, [SyntaxTypeExpr])
type SyntaxTySchemeExpr = (StdCoord, [String], [SyntaxTyPred], SyntaxTypeExpr)

data SyntaxValDef
    = SynValDef StdCoord Visibility String (Maybe SyntaxTySchemeExpr) (SyntaxExpr) -- Cordinate della definizione, nome del valore, espressione
    deriving Show

data SyntaxDataVariant
    = SynDataVariant StdCoord String [SyntaxTypeExpr] --Coordinate della definizione, nome della variante, lista di argomenti sia come tipo concreto (da assegnare in fase di tipizzazione), sia come espressione di tipi
    deriving Show

data SyntaxDataDef
    = SynDataDef StdCoord Visibility String [String] [SyntaxDataVariant] --Coordinate della definizione, nome del tipo, lista di tipi argomento e quantificatori corrispondenti (da assegnare in fase di tipizzazione), varianti del tipo
    deriving Show

data Visibility = Public | Private
    deriving Show

type SyntaxModRelValDecl = (StdCoord, String, SyntaxTySchemeExpr)
data SyntaxModDef
    = ModMod StdCoord Visibility String SyntaxModule
    | ModFromFile StdCoord Visibility String String
    | ModUse StdCoord Visibility Path
    | ModTypeSyn StdCoord Visibility String [String] SyntaxTypeExpr
    | ModValGroup [SyntaxValDef]
    | ModDataGroup [SyntaxDataDef]
    | ModRel StdCoord Visibility [SyntaxTyPred] String [String] [SyntaxModRelValDecl] --visibilità, superrels, nome, tyvars, corpo
    | ModInst StdCoord [String] [SyntaxTyPred] SyntaxTyPred [(StdCoord, String, SyntaxExpr)]-- visibilità, predicato quantificato da constraints con forall, definizioni
    | ModExt StdCoord Visibility String [SyntaxTypeExpr] SyntaxTypeExpr
    deriving Show
data SyntaxModule = Module [SyntaxModDef]
    deriving Show
