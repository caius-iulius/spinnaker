import System.IO
import System.Environment
import Data.Tree
import Control.Monad.State

import MPCL
import Parser
import PrettyPrinter
import Demod
import Typer
import Interpreter
import HLDefs
import TypingDefs
import OptimizeHL
import Monomorphizer

frontendCompile :: String -> IO (Either String (TypingEnv, HLExpr, BlockProgram))
frontendCompile fname = (>>= return . fst) $ runTyperState (0,0,0) $ do
    (denv, entry, block) <- demodProgram "stdlib/core" "stdlib/std" fname
    typerLog $ "DemodProgram:\n" ++ (drawTree $ toTreeBlockProgram block)
    (env, tyblock) <- typeBlockProgram block
    typerLog $ "Typed Program:\n" ++ (drawTree $ toTreeBlockProgram tyblock)
    return (env, entry, tyblock)

main = do {
    args <- getArgs;
    either <- frontendCompile (head args);
    let (ep, b) = case either of
            Left e -> error $ "Frontend compilation error: " ++ e
            Right (env, ep, block) -> (ep, block)
    ;
    prog <- monomorphizeProgram (ep, b);
    (ep', mono) <- return $ optimizeProgram prog;
    compLog $ "Mono EP: " ++ (drawTree $ toTreeHLExpr ep') ++ "\nDefs: " ++(drawTree $ toTreeMonoDefs mono);
    compLog $ "Unoptimized program size: " ++ show (programSize prog) ++ ", optimized program size: " ++ show (programSize (ep', mono));
    hFlush stdout;
    evalProgram (ep', mono)
}
