import System.IO
import System.Environment
import System.CPUTime
import Data.Tree
import Control.Monad.State

import qualified Paths_spinnaker as Paths

import CompDefs
import ArgParser
import HLDefs
import PrettyPrinter
import Parser.Demod
import Typer.TypingDefs
import Typer.Typer
import Monomorphizer
import OptimizeHL
import Defunctionalize
import MLDefs
import MLOps
import MLOptimize
import HLtoML
import VM.MLtoVM
import qualified VM.VM as VM
import MLtoJS

timeTyper :: TyperState t -> TyperState (t, Double)
timeTyper a = do
    start <- lift $ lift $ lift getCPUTime
    v <- a
    end <- lift $ lift $ lift getCPUTime
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

compile = do
    source <- fmap (forceGetArg "source_file") getArgOptions
    ((either, uid),t_frontend) <- time $ frontendCompile source
    let (ep, block, ts) = case either of
            Left e -> error $ "Frontend compilation error: " ++ e
            Right (env, ep, block, ts) -> (ep, block, ts)
    let typeddatasummary = blockProgramToDataSummary block --TODO sposta questa operazione in qualche altro file
    (prog, t_mono) <- time $ monomorphizeProgram (ep, block)
    (mono, t_opti) <- time $ return $ optimizeProgram prog
    compLog $ "Mono " ++ showMonoProg mono
    ((defundatasummary, defraw, uid'), t_defun) <- time $ defunProgram mono uid
    compLog $ "Final data summary: " ++ show (typeddatasummary ++ defundatasummary)
    (defopti, t_opti2) <- time $ return $ optimizeProgram defraw
    compLog $ "Defun " ++ showMonoProg defopti

    ((mlprog, uid''), t_toml) <- time $ hltoml defopti uid'
    let mlopti = optimizeMLProg mlprog
    compLog $ "MLProg " ++ showMLProg mlopti

    compLog $ "Unoptimized program size: " ++ show (programSize prog) ++ ", optimized program size: " ++ show (programSize mono) ++ ", defun program size: " ++ show (programSize defopti) ++ ", ML program size: " ++ show (mlprogramSize mlopti)
    compLog $ "Timings: frontend:" ++ show t_frontend ++ show ts ++ "ms mono:" ++ show t_mono ++ "ms opti:" ++ show t_opti ++ "ms defun:" ++ show t_defun ++ "ms opti2:" ++ show t_opti2 ++ "ms toml:" ++ show t_toml ++ "ms"

    backend <- fmap (forceGetArg "backend") getArgOptions
    case backend of
        "js" -> lift $ writeFile "out.js" $ tojsProgram (typeddatasummary ++ defundatasummary) mlopti
        "vm" -> do
            let vmprog = progToVm mlopti
            compLog $ "VM Bytecode: " ++ show vmprog
            lift $ hFlush stdout
            (_, t_eval) <- time $ lift $ VM.evalProg vmprog
            compLog $ "Program eval time:" ++ show t_eval ++ "ms"

argdefs =
    [ Arg {argID="help", argShort=Just 'h', argLong=Just "help", argIsOpt=True, argData=Nothing, argDesc="Display this message"}
    , Arg {argID="verbose", argShort=Just 'v', argLong=Just "verbose", argIsOpt=True, argData=Nothing, argDesc="Verbose compiler output"}
    , Arg {argID="source_file", argShort=Just 'f', argLong=Just "file", argIsOpt=False, argData=Just $ ArgDataStr Nothing, argDesc="Specify source code file"}
    , Arg {argID="backend", argShort=Nothing, argLong=Just "backend", argIsOpt=True, argData=Just $ ArgDataOpt ["js", "vm"] (Just "js"), argDesc="Specify the compiler backend"}
    ]

main = getArgs >>= \args ->
    case parseArgs argdefs args of
        Left _ -> putStr $ "The Spinnaker Compiler\n"++showHelp argdefs
        Right argparse -> do
            datadir <- Paths.getDataDir
            if gotArg "help" argparse then putStr $ "The Spinnaker Compiler\n"++showHelp argdefs else return ()
            runCompMon CompState{dataDir=datadir, argOptions=argparse} compile
