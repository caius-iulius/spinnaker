module MLDefs where
import Parser.MPCL(StdCoord)
import Typer.TypingDefs
import HLDefs (Literal)

data MLPattern
    = MLPLiteral Literal
    | MLPVariant String
    deriving Show

data MLExprData
    = MLLiteral Literal
    | MLLabel String
    | MLConstructor String [MLExpr]
    | MLCombinator String [MLExpr]
    | MLJoin String [MLExpr]
    | MLTest MLExpr [(MLPattern, MLExpr)] MLExpr
    | MLProj MLExpr String Int
    | MLLet String MLExpr MLExpr
    | MLLetJoin String [(String, DataType)] MLExpr MLExpr
    | MLError StdCoord String --TODO: la coordinata si può prendere dall'esterno, sostituisci la stringa con una reference al tipo di errore, oppure specializza solo al pattern matching, o ancora utilizza un'espressione esterna
    deriving Show

type MLExpr = (StdCoord, DataType, MLExprData)
type MLDef = (String, [(String, DataType)], MLExpr)
type MLProgram = (MLExpr, [MLDef])
