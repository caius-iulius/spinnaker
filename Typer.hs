module Typer (typeProgram) where
import HIRDefs
import Demod
import TypingDefs
import KindTyper
import TypeTyper
import qualified Data.Map as Map
import Control.Monad.Trans

typeBlockProgram (BlockProgram {-ddefs-} vdefgroups) = do
    (s, e, vdefgroups') <- typeValDefGroups initTypingEnv vdefgroups
    lift $ lift $ putStrLn $ "Final substitution: " ++ show s
    lift $ lift $ putStrLn $ "Final env: " ++ show e
    lift $ lift $ putStrLn $ "Final env freetyvars: " ++ show (freetyvars e)
    return (BlockProgram vdefgroups')

typeProgram :: HIRModule -> IO (Either String BlockProgram)
typeProgram program = do
    eitherBlock <- demodProgram program
    case eitherBlock of
        Left e -> return $ Left e
        Right (_, block) -> (runTyperState $ typeBlockProgram block) >>= return . fst
    --eitherBlock >>= \(_,block) -> runTyperState $ typeBlockProgram block
