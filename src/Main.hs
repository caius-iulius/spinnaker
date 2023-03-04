import System.IO
import System.Environment
import System.CPUTime
import Data.Tree
import Control.Monad.State

import Paths_spinnaker

import HLDefs
import PrettyPrinter
import Parser.Demod
import Typer.TypingDefs
import Typer.Typer
import Monomorphizer
import OptimizeHL
import Defunctionalize
import HLtoML
import VM.MLtoVM
import qualified VM.VM as VM

time :: IO t -> IO (t, Double)
time a = do
    start <- getCPUTime
    v <- a
    end <- getCPUTime
    let diff = fromIntegral (end - start) / (10^9)
    return (v, diff)

timeTyper :: TyperState t -> TyperState (t, Double)
timeTyper a = do
    start <- lift $ lift getCPUTime
    v <- a
    end <- lift $ lift getCPUTime
    let diff = fromIntegral (end - start) / (10^9)
    return (v, diff)

frontendCompile fname = fmap (\(either, (uid, _, _)) -> (either, uid)) $ runTyperState (0,0,0) $ do
    rootpath <- lift $ lift getDataDir
    typerLog $ "Current data dir: " ++ rootpath
    ((denv, entry, block), t_demod) <- timeTyper $ demodProgram (rootpath ++ "/")  "stdlib/core.spk" "stdlib/std.spk" fname
    typerLog $ "DemodProgram:\n" ++ drawTree (toTreeBlockProgram block)
    ((env, tyblock), t_typer) <- timeTyper $ typeBlockProgram block
    typerLog $ "Typed Program:\n" ++ drawTree (toTreeBlockProgram tyblock)
    return (env, entry, tyblock, (t_demod, t_typer))

main = do {
    args <- getArgs;
    ((either, uid),t_frontend) <- time $ frontendCompile (head args);
    let (ep, block, ts) = case either of
            Left e -> error $ "Frontend compilation error: " ++ e
            Right (env, ep, block, ts) -> (ep, block, ts)
    ;
    let typeddatasummary = blockProgramToDataSummary block --TODO sposta questa operazione in qualche altro file
    ;
    (prog, t_mono) <- time $ monomorphizeProgram (ep, block);
    (mono, t_opti) <- time $ return $ optimizeProgram prog;
    compLog $ "Mono " ++ showMonoProg mono;
    ((defundatasummary, defraw, uid'), t_defun) <- time $ defunProgram mono uid;
    compLog $ "Final data summary: " ++ show (typeddatasummary ++ defundatasummary);
    (defopti, t_opti2) <- time $ return $ optimizeProgram defraw;
    compLog $ "Defun " ++ showMonoProg defopti;

    (mlprog, uid'') <- hltoml defopti uid';
    compLog $ "MLProg " ++ showMLProg mlprog;

    (vmprog, t_tovm) <- time $ return $ progToVm mlprog;
    compLog $ "VM Bytecode: " ++ show vmprog;
    compLog $ "Unoptimized program size: " ++ show (programSize prog) ++ ", optimized program size: " ++ show (programSize mono) ++ ", defun program size: " ++ show (programSize defopti);
    compLog $ "Timings: frontend:" ++ show t_frontend ++ show ts ++ "ms mono:" ++ show t_mono ++ "ms opti:" ++ show t_opti ++ "ms defun:" ++ show t_defun ++ "ms opti2:" ++ show t_opti2 ++ "ms tovm:" ++ show t_tovm ++ "ms";
    hFlush stdout;
    (_, t_eval) <- time $ VM.evalProg vmprog;
    compLog $ "Program eval time:" ++ show t_eval ++ "ms";
}
