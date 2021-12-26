module Typer (typeProgram) where
import HIRDefs
import TypingDefs
import KindTyper
import TypeTyper
import qualified Data.Map as Map
import Control.Monad.Trans

builtinTypes =
    [   ("->", KFun KStar (KFun KStar KStar))
    ,   ("Int", KStar)
    ,   ("Flt", KStar)
    ]
initEnv = (TypingEnv Map.empty (Map.fromList builtinTypes) Map.empty)

typeProgramM (Program ddefs vdefss) = do
    (s, e, typed) <- typeValDefsGroups initEnv vdefss
    lift $ lift $ putStrLn $ "Final substitution: " ++ show s
    lift $ lift $ putStrLn $ "Final env: " ++ show e
    return (Program ddefs typed)

typeProgram :: HIRProgram -> IO (Either String HIRProgram)
typeProgram program = do
    (either, _) <- runTyperState $ typeProgramM program
    return either
