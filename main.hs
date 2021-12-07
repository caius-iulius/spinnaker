import System.IO
import System.Environment

import Parser
import PrettyPrinter
import MPCL
import Data.Tree

main = do {
    args <- getArgs;
    handle <- openFile (head args) ReadMode;
    contents <- hGetContents handle;
    putStrLn "Program:";
    putStrLn contents;
    case parse getProgram (Coord (head args) 1 1, contents) of
        POk progdefslist _ -> putStrLn $ drawTree $ Node "Parsed" (map toTreeHIRProgramDefs progdefslist)
        pe -> print pe
}
