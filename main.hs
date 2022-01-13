import System.IO
import System.Environment

import MPCL
import Parser
import PrettyPrinter
import Data.Tree
import Typer

coreModule = do { --NOTE: Non dà messaggi di errore se il parsing del Core fallisce
    handle <- openFile "core" ReadMode;
    contents <- hGetContents handle;
    let POk coreParsed _ = parse getProgram (Coord "Core" 1 1, contents)
        in return coreParsed
}

main = do {
    args <- getArgs;
    handle <- openFile (head args) ReadMode;
    contents <- hGetContents handle;
    putStrLn "Program:";
    putStrLn contents;
    case parse getProgram (Coord (head args) 1 1, contents) of
        POk untyped _ -> do {
            core <- coreModule;
            putStrLn $ drawTree $ Node "Parsed" [toTreeSynMod untyped];
            either <- typeProgram core untyped;
            case either of
                Left e -> putStrLn $ "Typing error: " ++ e
                Right typed -> putStrLn $ drawTree $ Node "Typed TEMPORARY" [toTreeBlockProgram typed]
        }
        pe -> print pe
}
