module Typer (typeProgram) where
import HIRDefs
import TypingDefs
import TypeTyper
import qualified Data.Map as Map
import Control.Monad.Trans

typeProgramM (Program ddefs vdefss) = let init_env = (TypingEnv Map.empty Map.empty Map.empty) in do
    (s, e, typed) <- typeValDefsGroups init_env vdefss
    lift $ lift $ putStrLn $ "Final substitution: " ++ show s
    lift $ lift $ putStrLn $ "Final env: " ++ show e
    return (Program ddefs typed)

typeProgram :: HIRProgram -> IO (Either String HIRProgram)
typeProgram program = do
    (either, _) <- runTyperState $ typeProgramM program
    return either
