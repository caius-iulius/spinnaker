import System.IO
import System.Environment
import System.CPUTime
import Data.Tree
import Control.Monad.State

import PrettyPrinter
import Demod
import Typer
import HLDefs
import TypingDefs
import OptimizeHL
import Monomorphizer
import HLtoVM
import qualified VM as VM

time :: IO t -> IO (t, Double)
time a = do
    start <- getCPUTime
    v <- a
    end <- getCPUTime
    let diff = (fromIntegral (end - start)) / (10^9)
    return (v, diff)

frontendCompile :: String -> IO (Either String (TypingEnv, HLExpr, BlockProgram))
frontendCompile fname = (>>= return . fst) $ runTyperState (0,0,0) $ do
    (denv, entry, block) <- demodProgram "stdlib/core" "stdlib/std" fname
    typerLog $ "DemodProgram:\n" ++ (drawTree $ toTreeBlockProgram block)
    (env, tyblock) <- typeBlockProgram block
    typerLog $ "Typed Program:\n" ++ (drawTree $ toTreeBlockProgram tyblock)
    return (env, entry, tyblock)

main = do {
    args <- getArgs;
    (either,t_frontend) <- time $ frontendCompile (head args);
    let (ep, b) = case either of
            Left e -> error $ "Frontend compilation error: " ++ e
            Right (env, ep, block) -> (ep, block)
    ;
    (prog, t_mono) <- time $ monomorphizeProgram (ep, b);
    ((ep', mono), t_opti) <- time $ return $ optimizeProgram prog;
    compLog $ "Mono EP: " ++ (drawTree $ toTreeHLExpr ep') ++ "\nDefs: " ++(drawTree $ toTreeMonoDefs mono);
    (vmprog, t_tovm) <- time $ return $ progToVm (ep', mono);
    compLog $ "VM Bytecode: " ++ show vmprog;
    compLog $ "Unoptimized program size: " ++ show (programSize prog) ++ ", optimized program size: " ++ show (programSize (ep', mono));
    compLog $ "Timings: frontend:" ++ show t_frontend ++ "ms mono:" ++ show t_mono ++ "ms opti:" ++ show t_opti ++ "ms tovm:" ++ show t_tovm ++ "ms";
    hFlush stdout;
    (_, t_eval) <- time $ VM.evalProg vmprog;
    compLog $ "Program eval time:" ++ show t_eval ++ "ms"
}
