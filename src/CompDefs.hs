module CompDefs where
import Control.Monad.Reader
import System.CPUTime
import System.Environment
import ArgParser

data CompState = CompState {
    dataDir :: String,
    argOptions :: Parse
    }

type CompMon = ReaderT CompState IO
runCompMon = flip runReaderT

getDataDir :: CompMon String
getDataDir = asks dataDir

getArgOptions :: CompMon Parse
getArgOptions = asks argOptions

compLog :: String -> CompMon ()
compLog l = do
    opts <- getArgOptions
    if gotArg "verbose" opts
    then lift $ putStrLn l
    else return ()

time :: CompMon t -> CompMon (t, Double)
time a = do
    start <- lift getCPUTime
    v <- a
    end <- lift getCPUTime
    let diff = fromIntegral (end - start) / (10^9)
    return (v, diff)

