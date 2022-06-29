module Interpreter where
import qualified Data.Map as Map
import Control.Monad.Reader
import Data.Char
import Data.Maybe(isJust, catMaybes)
import Data.List(partition)
import Data.Tree

import MPCL(StdCoord(..), dummyStdCoord)
import PrettyPrinter
import TypingDefs
import MGUs
import TypeTyper(substApplyExpr)
import HLDefs


type InterpEnv = Map.Map String [(DataType, HLExpr)]
type InterpState t = ReaderT InterpEnv IO t

findEnvVal :: InterpEnv -> String -> DataType -> Maybe HLExpr
findEnvVal env l t = Map.lookup l env >>= getMostSpecific
    where reduceMostSpecifics :: [(DataType, HLExpr)]->[(DataType, HLExpr)]->[(DataType, HLExpr)]
          reduceMostSpecifics sps [] = sps
          reduceMostSpecifics sps ((te, e):tses')
            | any (\(te', _) -> isJust (match dummyStdCoord te te')) (sps ++ tses')
                = reduceMostSpecifics sps tses'
            | otherwise =  reduceMostSpecifics ((te, e):sps) tses'
          getMostSpecific tses =
            let matching = catMaybes [match dummyStdCoord te t >> Just (te, e) | (te, e) <- tses]
                specifics = reduceMostSpecifics [] matching
            in case specifics of
                [] -> error $ "No matching istances of: " ++ show l ++ " with type: " ++ show t
                ((te, e):[]) -> do
                    s <- match dummyStdCoord te t
                    Just (substApplyExpr s e)
                xs -> error $ "Cannot find most specific instance of: " ++ show l ++ " with type: " ++ show t ++ "\n    Possible instances are: " ++ show (map fst xs)

sievePatternInner :: HLPatternData -> HLExpr -> Maybe (Map.Map String HLExpr)
sievePatternInner PatWildcard _ = return Map.empty
sievePatternInner (PatLiteral plit) (_, _, ExprLiteral elit) =
    if plit == elit then return Map.empty else Nothing
sievePatternInner (PatVariant pvar ps) (_, _, ExprConstructor evar es) =
    if pvar == evar then do
        maps <- zipWithM sievePattern ps es
        return $ Map.unions maps
    else Nothing
sievePatternInner p e = error $ show p ++ " : \n\n" ++ (drawTree $ toTreeHLExpr e)

sievePattern :: HLPattern -> HLExpr -> Maybe (Map.Map String HLExpr)
sievePattern (_, Nothing, patdata) e = sievePatternInner patdata e
sievePattern (_, Just l, patdata) e = do
    inner <- sievePatternInner patdata e
    return $ Map.union inner (Map.singleton l e)

getBindsInner :: HLPatternData -> [String]
getBindsInner PatWildcard = []
getBindsInner (PatLiteral _) = []
getBindsInner (PatVariant _ ps) = join $ map getBinds ps

getBinds :: HLPattern -> [String]
getBinds (_, Nothing, patdata) = getBindsInner patdata
getBinds (_, Just l, patdata) = l : getBindsInner patdata

exprSubstApply :: Map.Map String HLExpr -> HLExpr -> HLExpr
exprSubstApply _ e@(_, _, ExprLiteral _) = e
exprSubstApply s (c, dt, ExprApp e0 e1) = (c, dt, ExprApp (exprSubstApply s e0) (exprSubstApply s e1))
exprSubstApply s e@(_, _, ExprLabel l) =
    case Map.lookup l s of
        Nothing -> e
        Just expr -> expr
exprSubstApply s (c, dt, ExprConstructor v es) = (c, dt, ExprConstructor v (map (exprSubstApply s) es))
exprSubstApply s (c, dt, ExprLambda pat ret) =
    let
        s' = foldl (flip Map.delete) s (getBinds pat)
    in (c, dt, ExprLambda pat (exprSubstApply s' ret))
exprSubstApply s (c, dt, ExprPut val pses) =
    let
        peSubstApply (p, e) = (p, exprSubstApply (foldl (flip Map.delete) s (getBinds p)) e)
    in (c, dt, ExprPut (exprSubstApply s val) (map peSubstApply pses))

builtinApply :: String -> HLExpr -> InterpState HLExprData
builtinApply "_addInt#BI" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = return $ ExprLiteral $ LitInteger (i0 + i1)
builtinApply "_subInt#BI" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = return $ ExprLiteral $ LitInteger (i0 - i1)
builtinApply "_mulInt#BI" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = return $ ExprLiteral $ LitInteger (i0 * i1)
builtinApply "_divInt#BI" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = return $ ExprLiteral $ LitInteger (div i0 i1)
builtinApply "_equInt#BI" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = return $ ExprConstructor (if i0 == i1 then "True#BI" else "False#BI") []
builtinApply "_neqInt#BI" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = return $ ExprConstructor (if i0 /= i1 then "True#BI" else "False#BI") []
builtinApply "_leqInt#BI" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = return $ ExprConstructor (if i0 <= i1 then "True#BI" else "False#BI") []
builtinApply "_greInt#BI" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = return $ ExprConstructor (if i0 > i1 then "True#BI" else "False#BI") []
builtinApply "_putChr#BI" (_, _, ExprLiteral (LitInteger i)) = do
    lift $ putChar $ chr i
    return $ ExprConstructor "()0" []
builtinApply "_getChr#BI" (_, _, ExprConstructor "()0" []) = do
    c <- lift $ getChar
    return $ ExprLiteral $ LitInteger $ ord c

builtinApply l e = error $ "TODO builtinApply: " ++ l

choosePattern :: StdCoord -> HLExpr -> [(HLPattern, HLExpr)] -> InterpState HLExpr
choosePattern c _ [] = error $ show c ++ " Non-exhausive putexpr"
choosePattern c val ((p, e):pses) =
    case sievePattern p val of
        Nothing -> choosePattern c val pses
        Just s -> eval $ exprSubstApply s e

eval :: HLExpr -> InterpState HLExpr
eval e@(_, _, ExprLiteral l) = return e
eval (_, _, ExprApp f a) = do
    f' <- eval f
    a' <- eval a
    case f' of
        --(c, DataTypeApp _ at, ExprConstructor v es) -> return (c, at, ExprConstructor v (es++[a']))
        (c, DataTypeApp _ at, ExprLabel bilab) -> do
            bicall <- builtinApply bilab a'
            return (c, at, bicall)
        (_, _, ExprLambda pat ret) -> case sievePattern pat a' of
                Nothing -> error $ "WHAT SIEVE: " ++ show pat ++ " val " ++ show a'
                Just s -> eval $ exprSubstApply s ret
eval e@(c, dt, ExprLabel l) = do
    env <- ask
    case findEnvVal env l dt of
        Just expr -> eval expr
        Nothing -> return e
eval e@(c, dt, ExprConstructor l es) = do
    es' <- mapM eval es
    return (c, dt, ExprConstructor l es')
eval e@(_, _, ExprLambda _ _) = return e
eval e@(c, dt, ExprPut val pses) = do
    val' <- eval val
    choosePattern c val' pses

myListMerge :: Eq k => [(k,v)]->[(k,[v])]
myListMerge [] = []
myListMerge ((k,v):kvs) =
    let (isk, isntk) = partition ((k==) . fst) kvs
        in (k, v:map snd isk):myListMerge isntk

evalProgram :: (String, BlockProgram) -> IO HLExpr
evalProgram (entryPoint, BlockProgram datagroups reldefs valgroups instdefs) =
    let
        valbinds = join valgroups
        valVtables = map (\(ValDef _ l _ _ e@(_, t, _))->(l, [(t, e)])) valbinds
        instsList = myListMerge $ map (\(InstDef _ (Qual _ (Pred l _)) cles) -> (l, cles)) instdefs
        instsListTEs = map (\(il, cless) -> (il, map (\(c, l, e@(_, t, _))->(l, (t, e))) (concat cless))) instsList
        instsVtables :: [(String, [(DataType, HLExpr)])]
        instsVtables = concat $ map (myListMerge . snd) instsListTEs

        env = Map.fromList (valVtables ++ instsVtables)
    in do
        putStrLn $ "Interpreter VTABLEs: " ++ show (map (\(l, tses)->(l, map fst tses)) $ Map.toList env)
        putStrLn $ "\n---- ESEGUO IL PROGRAMMA ----"
        runReaderT (eval (Coord "interpreter" 0 0, buildTupType [], ExprLabel entryPoint)) env
    --TODO: così main può avere soltanto il tipo: (), il che non viene controllato nel typer
