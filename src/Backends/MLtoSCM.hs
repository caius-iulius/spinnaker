module Backends.MLtoSCM where
import Control.Monad.State
import Data.Maybe(fromJust, fromMaybe)
import Data.Char(ord)
import HLDefs
import MLDefs
import ML.MLOps

type IdentMap = [(String, String)]
type CodeGen a = State (Int, IdentMap, IdentMap, IdentMap, [String]) a

emit :: String -> CodeGen ()
emit code' = do
    (uid, var, comb, lab, code) <- get
    put (uid, var, comb, lab, code':code)

getVariant :: String -> CodeGen String
getVariant v = do
    (_, var, _, _, _) <- get
    return $ fromMaybe (show v) (lookup v var) -- se non si trova una variante significa che è una classe esterna, perciò il nome resta invariato

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
    put (uid+1, (v, show $ show uid):var, comb, lab, code)
    return (show $ show uid)

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

toscmLit :: Literal -> String
toscmLit (LitInteger i) = show i
toscmLit (LitFloating f) = show f
toscmLit (LitCharacter c) = "(spinnaker_comp_chrLit " ++ show (ord c) ++ ")"

variantAccess :: Int -> String -> String
variantAccess n l = "(cadr" ++ cdrs n l ++ ")"
    where
        cdrs 0 myl = ' ':myl
        cdrs myn myl = "(cdr" ++ cdrs (myn - 1) myl ++ ")"

genTest :: String -> MLPattern -> CodeGen String
genTest l (MLPLiteral lit@(LitCharacter _)) = return $ "((char=? " ++ l ++ " " ++ toscmLit lit ++ ")"
genTest l (MLPLiteral lit) = return $ "((= " ++ l ++ " " ++ toscmLit lit ++ ")"
genTest l (MLPVariant "True") = return $ "(" ++ l ++ " "
genTest l (MLPVariant "False") = return $ "((not " ++ l ++ ") "
genTest l (MLPVariant v) = do
    v' <- getVariant v
    return $ "((string=? (car " ++ l ++ ") " ++ v' ++ ") "

toscmExpr :: MLExpr -> CodeGen String
toscmExpr (_, _, MLTest tv pes def) = do
    tv' <- toscmExpr tv
    l' <- newLabel
    conds <- mapM (\(p, e) -> do
        test <- genTest l' p
        e' <- toscmExpr e
        return $ test ++ e' ++ ")\n") pes
    def' <- toscmExpr def
    return $ "(let ((" ++ l' ++ " " ++ tv' ++ "))" ++ "(cond " ++ concat conds ++ "(#t " ++ def' ++ "))" ++ ")"
toscmExpr (_, _, MLError c s) = return $ "(error " ++ show(show c ++ s) ++ ")"
toscmExpr (_, _, MLProj e _ n) = do
    e' <- toscmExpr e
    return (variantAccess n e')
toscmExpr (_, _, MLLiteral lit) = return $ toscmLit lit
toscmExpr (_, _, MLLabel l) = getLabel l
toscmExpr (_, _, MLConstructor "True" []) = return "#t"
toscmExpr (_, _, MLConstructor "False" []) = return "#f"
toscmExpr (_, _, MLConstructor v es) = do
    v' <- getVariant v
    es' <- mapM toscmExpr es
    return $ "(list " ++ unwords (v' : es') ++ ")" --TODO interleave/intersperse
toscmExpr (_, _, MLCombinator c es) = do
    c' <- getCombinator c
    es' <- mapM toscmExpr es
    return $ "(" ++ unwords (c' : es') ++ ")"
toscmExpr (_, _, MLJoin j es) = do
    j' <- getLabel j
    es' <- mapM toscmExpr es
    return $ "(" ++ unwords (j' : es') ++ ")"
toscmExpr (_, _, MLLet l e0 e1) = do
    l' <- newMapLabel l
    e0' <- toscmExpr e0
    e1' <- toscmExpr e1
    return $ "(let ((" ++ l' ++ " " ++ e0' ++ "))\n" ++ e1' ++ ")"
toscmExpr (_, _, MLLetJoin j lts e0 e1) = do
    j' <- newMapLabel j
    e1' <- toscmExpr e1
    as <- mapM (newMapLabel . fst) lts
    e0' <- toscmExpr e0
    return $ "(let ((" ++ j' ++ " (lambda (" ++ unwords as ++ ") " ++ e0' ++ ")))\n" ++ e1' ++ ")"
    

toscmVariant :: [String] -> String -> Int -> CodeGen ()
toscmVariant vused vname numargs =
    if elem vname vused then const () <$> newMapVariant vname
    else return ()

toscmDataSummaries :: [String] -> [DataSummary] -> CodeGen ()
toscmDataSummaries vused summaries =
    let stripped = do
            (_, variants) <- summaries
            map (\(vname, args) -> (vname, length args)) variants
    in mapM_ (uncurry $ toscmVariant vused) stripped

toscmCombinators :: [MLDef] -> CodeGen ()
toscmCombinators combs = do
    mapM_ (\(c, _, _) -> newMapCombinator c) combs
    mapM_ (\(c, asts, e) -> do
            c' <- getCombinator c
            as <- mapM (newMapLabel . fst) asts
            let define = "(define (" ++ unwords (c':as) ++ ")\n"
            body <- toscmExpr e
            emit $ define ++ body ++ ")\n\n"
            ) combs

toscmProgram :: [DataSummary] -> MLProgram -> String
toscmProgram datasummaries (ep, defs) = concat $ reverse $ (\(_,(_,_,_,_,code))->code) $ flip runState (0, [], [], [], []) $ do
    let vused = variantsUsedProg (ep, defs)
    toscmDataSummaries vused datasummaries
    toscmCombinators defs
    ep' <- toscmExpr ep
    emit ep'
