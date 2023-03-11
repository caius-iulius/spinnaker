module ArgParser where
import Control.Monad(join)
import Data.List(intercalate, transpose, partition)
import Data.Maybe(fromJust, isJust, catMaybes)
import System.Environment

data Arg =
    Arg {
        argID    :: String,
        argShort :: Maybe Char,
        argLong  :: Maybe String,
        argIsOpt :: Bool,
        argData  :: Maybe ArgData,
        argDesc  :: String
    }

data ArgData
    = ArgDataStr (Maybe String)
    | ArgDataOpt [String] (Maybe String)
    -- | ArgDataInt (Maybe Int)
    -- | ArgDataFlt (Maybe Float)

showDefault :: (a -> String) -> Maybe a -> String
showDefault _ Nothing = ""
showDefault f (Just d) = " (default=" ++ f d ++ ")"

showArgData (ArgDataStr s) = "<string>" ++ showDefault id s
showArgData (ArgDataOpt opts s) = intercalate "|" opts ++ showDefault id s
--showArgData (ArgDataInt s) = "<int>" ++ showDefault show s
--showArgData (ArgDataFlt s) = "<flt>" ++ showDefault show s

getHelpColumns :: Arg -> [String]
getHelpColumns arg = [maybe "" (('-':) . (:[])) (argShort arg), maybe "" ("--"++) (argLong arg), if argIsOpt arg then "[opt]" else "", maybe "" showArgData (argData arg), argDesc arg]

showHelp :: [Arg] -> String
showHelp args =
    let aass = map getHelpColumns args
        maxlens = map (maximum . map length) $ transpose aass
        pad len s = s ++ replicate (len - length s) ' '
        aasspadded = map (zipWith pad maxlens) aass
    in unlines $ map (intercalate "  ") aasspadded

type Parse = [(String, Maybe String)]
parseArgs :: [Arg] -> [String] -> Either String Parse
parseArgs = inner []
  where inner :: Parse -> [Arg] -> [String] -> Either String Parse
        inner parse defs [] = do
            defaults <- checkRemaining defs
            return $ catMaybes defaults ++ parse
        inner parse defs (arg:args) = do
            (def, defs') <- getDef arg defs
            case argData def of
                Nothing -> inner ((argID def, Nothing):parse) defs' args 
                Just argdata -> case args of
                    [] -> Left $ "expected some data after the argument: " ++ argID def
                    a:args' -> checkData argdata a >> inner ((argID def, Just a):parse) defs' args'
        getDef arg defs =
            case partition (\def -> elem arg $ catMaybes [('-':).(:[]) <$> argShort def, ("--"++) <$> argLong def]) defs of
                ([], _) -> Left $ "unrecognized argument: " ++ arg
                ([def], defs') -> return (def, defs')
        checkData (ArgDataStr _) _ = return ()
        checkData (ArgDataOpt opts _) d = if elem d opts then return () else Left $ d ++ " is not a valid option (" ++ intercalate "|" opts ++ ")"
        checkRemaining = mapM (\arg ->
                    case argData arg of
                        Just (ArgDataStr (Just def)) -> return $ Just (argID arg, Just def)
                        Just (ArgDataOpt _ (Just def)) -> return $ Just (argID arg, Just def)
                        _ -> if argIsOpt arg then return Nothing else Left $ "expected non-optional argument: " ++ argID arg
                )

parseArgsIO :: [Arg] -> IO Parse
parseArgsIO defs = do
    args <- getArgs
    case parseArgs defs args of
        Left e -> error e
        Right p -> return p

gotArg :: String -> Parse -> Bool
gotArg = (isJust .) . lookup
getArg :: String -> Parse -> Maybe String
getArg = (join .) . lookup
forceGetArg = (fromJust .) . getArg
