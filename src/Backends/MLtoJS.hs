module Backends.MLtoJS where
import GHC.Unicode(isPrint, isSpace)
import Control.Monad.State
import Data.Maybe(fromJust, fromMaybe)
import HLDefs
import MLDefs
import ML.MLOps
import Typer.TypingDefs(isTupLabl)

type IdentMap = [(String, String)]
type CodeGen a = State (Int, IdentMap, IdentMap, IdentMap, [String]) a

emit :: String -> CodeGen ()
emit code' = do
    (uid, var, comb, lab, code) <- get
    put (uid, var, comb, lab, code':code)

getVariant :: String -> CodeGen String
getVariant v = let (istup, n) = isTupLabl v in
    if istup then return $ "Tup"++show n
    else do
    (_, var, _, _, _) <- get
    return $ fromMaybe v (lookup v var) -- se non si trova una variante significa che è una classe esterna, perciò il nome resta invariato

getCombinator :: String -> CodeGen String
getCombinator c = do
    (_, _, comb, _, _) <- get
    return $ fromMaybe c (lookup c comb) -- se non si trova un combinatore significa che è una funzione esterna, perciò il nome resta invariato

getLabel :: String -> CodeGen String
getLabel l = do
    (_, _, _, lab, _) <- get
    return $ fromJust $ lookup l lab

newLabel :: CodeGen String
newLabel = do
    (uid, var, comb, lab, code) <- get
    put (uid+1, var, comb, lab, code)
    return ("label"++show uid)

newMapVariant :: String -> CodeGen String
newMapVariant v = do
    (uid, var, comb, lab, code) <- get
    put (uid+1, (v, "Variant"++show uid):var, comb, lab, code)
    return ("Variant"++show uid)

newMapCombinator :: String -> CodeGen String
newMapCombinator c = do
    (uid, var, comb, lab, code) <- get
    put (uid+1, var, (c, "combinator"++show uid):comb, lab, code)
    return ("combinator"++show uid)

newMapLabel :: String -> CodeGen String
newMapLabel l = do
    (uid, var, comb, lab, code) <- get
    put (uid+1, var, comb, (l,"label"++show uid):lab, code)
    return ("label"++show uid)

toCommaList :: [String] -> String
toCommaList [] = ""
toCommaList [x] = x
toCommaList (x:xs) = x ++ ", " ++ toCommaList xs

tojsLit :: Literal -> String
tojsLit (LitInteger i) = show i
tojsLit (LitFloating f) = show f
tojsLit (LitCharacter c)
    | isSpace c || elem c "\\\"\'" = show c
    | isPrint c = ['\"', c, '\"']
    | otherwise = show c

emitTest :: String -> MLPattern -> CodeGen ()
emitTest l (MLPLiteral lit) = emit $ "if(" ++ l ++ " === " ++ tojsLit lit ++ "){\n"
emitTest l (MLPVariant "True") = emit $ "if(" ++ l ++ "){\n"
emitTest l (MLPVariant "False") = emit $ "if(!" ++ l ++ "){\n"
emitTest l (MLPVariant v) = do
    v' <- getVariant v
    emit $ "if(" ++ l ++ " instanceof " ++ v' ++ "){\n"

tojsBlock :: (String -> String) -> MLExpr -> CodeGen ()
tojsBlock final (_, _, MLLet l e0 e1) = do
    l' <- newMapLabel l
    e0' <- tojsExpr e0
    emit $ "let " ++ l' ++ " = " ++ e0' ++ ";\n"
    tojsBlock final e1
tojsBlock final (_, _, MLTest tv pes def) = do
    tv' <- tojsExpr tv
    l' <- newLabel
    emit $ "let " ++ l' ++ " = " ++ tv' ++ ";\n"
    mapM_ (\(p, e) -> do
        emitTest l' p
        tojsBlock final e
        emit "} else ") pes
    emit "{\n"
    tojsBlock final def
    emit "}\n"
tojsBlock final (_, _, MLError c s) = emit $ "throw new Error(" ++ show(show c ++ s) ++ ");\n"
tojsBlock final other = do
    expr <- tojsExpr other
    emit $ final expr

tojsExpr :: MLExpr -> CodeGen String
tojsExpr (_, _, MLLiteral lit) = return $ tojsLit lit
tojsExpr (_, _, MLLabel l) = getLabel l
tojsExpr (_, _, MLConstructor "True" []) = return "true"
tojsExpr (_, _, MLConstructor "False" []) = return "false"
tojsExpr (_, _, MLProj e _ n) = do
    e' <- tojsExpr e
    return $ "(" ++ e' ++ ")[" ++ show n ++ "]"
tojsExpr (_, _, MLConstructor v es) = do
    v' <- getVariant v
    es' <- mapM tojsExpr es
    return $ "new " ++ v' ++ "(" ++ toCommaList es' ++ ")"
tojsExpr (_, _, MLCombinator c es) = do
    c' <- getCombinator c
    es' <- mapM tojsExpr es
    return $ c' ++ "(" ++ toCommaList es' ++ ")"
tojsExpr (_, _, MLJoin j es) = do
    j' <- getLabel j
    es' <- mapM tojsExpr es
    return $ j' ++ "(" ++ toCommaList es' ++ ")"
tojsExpr (_, _, MLLet l e0 e1) = do
    l' <- newMapLabel l
    e0' <- tojsExpr e0
    emit $ "let " ++ l' ++ " = " ++ e0' ++ ";\n"
    tojsExpr e1
tojsExpr (_, _, MLLetJoin j lvs e0 e1) = do
    j' <- newMapLabel j
    as <- mapM (newMapLabel . fst) lvs
    emit $ "let " ++ j' ++ " = function(" ++ toCommaList as ++ "){\n"
    tojsBlock (\e' -> "return " ++ e' ++ ";\n") e0
    emit "};\n"
    tojsExpr e1
tojsExpr other = do
    l <- newLabel
    emit $ "let " ++ l ++ ";\n"
    tojsBlock (\e -> l ++ " = " ++ e ++ ";\n") other
    return l

tojsVariant :: [String] -> String -> Int -> CodeGen ()
tojsVariant vused vname numargs =
    if not (elem vname vused) then return ()
    else do
        vname' <- newMapVariant vname
        let args = map (("x"++) . show) [0..numargs-1]
        emit $ "class " ++ vname' ++ "{\nconstructor(" ++ toCommaList args ++ "){\n"
        mapM_ (\(n, arg) -> emit $ "this["++show n++"] = " ++ arg ++ ";\n"
                ) $ zip [0..] args
        emit "}\n}\n\n"

tojsDataSummaries :: [String] -> [DataSummary] -> CodeGen ()
tojsDataSummaries vused summaries =
    let stripped = do
            (_, variants) <- summaries
            map (\(vname, args) -> (vname, length args)) variants
    in mapM_ (uncurry $ tojsVariant vused) stripped

tojsCombinators :: [MLDef] -> CodeGen ()
tojsCombinators combs = do
    mapM_ (\(c, _, _) -> newMapCombinator c) combs
    mapM_ (\(c, asts, e) -> do
            c' <- getCombinator c
            as <- mapM (newMapLabel . fst) asts
            emit $ "function " ++ c' ++ "(" ++ toCommaList as ++ "){\n"
            tojsBlock (\e' -> "return " ++ e' ++ ";\n") e
            emit "}\n\n"
            ) combs

tojsProgram :: [DataSummary] -> MLProgram -> String
tojsProgram datasummaries (ep, defs) = concat $ reverse $ (\(_,(_,_,_,_,code))->code) $ flip runState (0, [], [], [], []) $ do
    let vused = variantsUsedProg (ep, defs)
    tojsDataSummaries vused datasummaries
    tojsCombinators defs
    tojsBlock (++ ";\n") ep
