import System.IO
import System.Environment

import MPCL
import Parser
import PrettyPrinter
import Data.Tree
import Typer
import Interpreter
import HLDefs

coreModule = do { --NOTE: Non dà messaggi di errore se il parsing del Core fallisce
    handle <- openFile "core" ReadMode;
    contents <- hGetContents handle;
    let POk coreParsed _ = parse getProgram (Coord "Core" 1 1, contents)
        in return coreParsed
}

testCompile :: IO (String, BlockProgram)
testCompile = do {
    args <- getArgs;
    handle <- openFile (head args) ReadMode;
    contents <- hGetContents handle;
    putStrLn "Program:";
    putStrLn contents;
    case parse getProgram (Coord (head args) 1 1, contents) of
        POk untyped _ -> do {
            core <- coreModule;
            putStrLn $ drawTree $ Node "Parsed Core" [toTreeSynMod core];
            putStrLn $ drawTree $ Node "Parsed" [toTreeSynMod untyped];
            either <- typeProgram core untyped;
            case either of
                Left e -> error $ "Typing error: " ++ e
                Right typed -> do {
                    putStrLn $ drawTree $ Node ("Typed TEMPORARY, entryPoint: " ++ fst typed) [toTreeBlockProgram $ snd typed];
                    return typed
                }
        }
        pe -> error $ show pe
}

main = do {
    compiled <- testCompile;
    result <- evalProgram compiled;
    putStrLn $ "Result: " ++ (drawTree $ toTreeHLExpr result)
}
