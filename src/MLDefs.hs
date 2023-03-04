module MLDefs where
import Parser.MPCL(StdCoord)
import Typer.TypingDefs
import HLDefs (Literal)

data MLPattern
    = MLPLiteral Literal
    | MLPVariant String [String]
    deriving Show

data MLExprData
    = MLLiteral Literal
    | MLLabel String
    | MLConstructor String [MLExpr]
    | MLCombinator String [MLExpr]
    | MLTest String MLPattern MLExpr MLExpr
    | MLLet String MLExpr MLExpr
    | MLError StdCoord String --TODO: la coordinata si può prendere dall'esterno, sostituisci la stringa con una reference al tipo di errore, oppure specializza solo al pattern matching, o ancora utilizza un'espressione esterna
    deriving Show

type MLExpr = (StdCoord, DataType, MLExprData)
type MLDef = (String, [(String, DataType)], MLExpr)
type MLProgram = (MLExpr, [MLDef])


mlexprSize :: MLExpr -> Int
mlexprSize (_, _, MLLiteral _) = 1
mlexprSize (_, _, MLLabel _) = 1
mlexprSize (_, _, MLConstructor _ es) = 1 + sum (map mlexprSize es)
mlexprSize (_, _, MLCombinator _ es) = 1 + sum (map mlexprSize es)
mlexprSize (_, _, MLTest _ _ epos eneg) = 2 + mlexprSize epos + mlexprSize eneg
mlexprSize (_, _, MLLet _ e0 e1) = 1 + mlexprSize e0 + mlexprSize e1
mlexprSize (_, _, MLError _ _) = 1

mlprogramSize (ep, defs) = mlexprSize ep + sum (map (mlexprSize . (\(_,_,a)->a)) defs)
