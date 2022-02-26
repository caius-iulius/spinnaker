import System.IO
import System.Environment

import MPCL
import Parser
import PrettyPrinter
import Data.Tree
import Typer
import Interpreter
import HLDefs
import TypingDefs
import SyntaxDefs
import VariantComplete

coreModule = do { --NOTE: Non dà messaggi di errore se il parsing del Core fallisce
    handle <- openFile "core" ReadMode;
    contents <- hGetContents handle;
    case parse getProgram (Coord "Core" 1 1, contents) of
        POk coreParsed _ -> return coreParsed
        err -> error $ show err
}

frontendCompile :: SyntaxModule -> SyntaxModule -> IO (Either String (TypingEnv, String, BlockProgram))
frontendCompile core program = (>>= return . fst) $ runTyperState (0, 0, 0) $ do {
    (env, entryPoint, block) <- typeProgram core program;
    block' <- completeVariantProgram env block;
    (env', block'') <- typeBlockProgram block';
    return (env', entryPoint, block'')
}

testCompile :: IO (TypingEnv, String, BlockProgram)
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
            either <- frontendCompile core untyped;
            case either of
                Left e -> error $ "Typing error: " ++ e
                Right (env, entryPoint, block) -> do {
                    putStrLn $ drawTree $ Node ("Typed TEMPORARY, entryPoint: " ++ entryPoint) [toTreeBlockProgram $ block];
                    putStrLn $ "Final typingEnv: " ++ show env;
                    return (env, entryPoint, block)
                }
        }
        pe -> error $ show pe
}

main = do {
    (_, ep, b) <- testCompile;
    result <- evalProgram (ep, b);
    putStrLn $ "Result: " ++ (drawTree $ toTreeHLExpr result)
}
