import System.IO
import System.Environment

import Parser
import PrettyPrinter
import MPCL
import Data.Tree
import TypingDefs
import TypeTyper

main = do {
    args <- getArgs;
    handle <- openFile (head args) ReadMode;
    contents <- hGetContents handle;
    putStrLn "Program:";
    putStrLn contents;
    case parse getProgram (Coord (head args) 1 1, contents) of
        POk untyped _ -> do {
            -- Da qui in poi è tutto temporaneo
            putStrLn $ drawTree $ Node "Parsed" [toTreeHIRProgram untyped];
            (either, _) <- runTyperState $ typeProgram untyped;
            case either of
                Left e -> putStrLn $ "Typing error: " ++ e
                Right typed -> putStrLn $ drawTree $ Node "Typed TEMPORARY" [toTreeHIRProgram typed]
        }
        pe -> print pe
}
