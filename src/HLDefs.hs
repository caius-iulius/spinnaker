module HLDefs where
import Parser.MPCL(StdCoord)
import Typer.TypingDefs

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
type HLPattern = (StdCoord, DataType, Maybe String, HLPatternData) -- coordinate, eventuale assegnazione del valore (tipo haskell labl@pat) e pattern vero e proprio

data HLExprData
    = ExprLiteral Literal --Valore letterale
    | ExprApp HLExpr HLExpr --Funzione, argomento
    | ExprLabel String --Riferimento a label
    | ExprConstructor String [HLExpr] -- Riferimento a una variante e argomenti "applicati"
    | ExprCombinator String [HLExpr] -- Riferimento al combinatore e argomenti
    | ExprLambda String HLExpr --Argomento e valore interno
    | ExprPut [HLExpr] [([HLPattern], HLExpr)] --Valore da controllare, lista di pattern e i branch corrispondenti
    | ExprHint DataType HLExpr --type hint di un'espressione
    deriving Show
type HLExpr = (StdCoord, DataType, HLExprData)

data HLValDef
    = ValDef StdCoord String (Maybe (Qual DataType)) [Pred] HLExpr -- Cordinate della definizione, nome del valore, type hint, espressione
    deriving Show

data HLExtDef = ExtDef StdCoord String String [DataType] DataType
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

type DataSummary = (DataType, [(String, [DataType])])
blockProgramToDataSummary :: BlockProgram -> [DataSummary]
blockProgramToDataSummary (BlockProgram ddefgroups _ _ _ _) = do
    ddefs <- ddefgroups
    flip map ddefs $ \(DataDef _ l qs variants) ->
        let datakind = dataQsToKind qs
            datatype = foldl DataTypeApp (DataTypeName l datakind) $ map (DataQuant . snd) qs
            variantinfo = map (\(DataVariant _ vl csds) -> (vl, map snd csds)) variants
        in (datatype, variantinfo)

type Inline = Bool
type Combinator = (String, Inline, [(String, DataType)], HLExpr)
type MonoProgram = (HLExpr, [Combinator])
