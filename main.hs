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
import OptimizeHL
import Monomorphizer

frontendCompile :: String -> IO (Either String (TypingEnv, HLExpr, BlockProgram))
frontendCompile fname = (>>= return . fst) $ runTyperState (0,0,0) $ typeProgram fname

main = do {
    args <- getArgs;
    either <- frontendCompile (head args);
    let (ep, b) = case either of
            Left e -> error $ "Frontend compilation error: " ++ e
            Right (env, ep, block) -> (ep, block)
    ;
    prog <- monomorphizeProgram (ep, b);
    (ep', mono) <- return $ optimizeProgram prog;
    putStrLn $ "Mono EP: " ++ (drawTree $ toTreeHLExpr ep') ++ "\nDefs: " ++(drawTree $ toTreeMonoDefs mono);
    putStrLn $ "Unoptimized program size: " ++ show (programSize prog) ++ ", optimized program size: " ++ show (programSize (ep', mono));
    hFlush stdout;
    evalProgram (ep', mono)
}
