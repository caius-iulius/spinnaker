module Interpreter where
import System.IO
import qualified Data.Map as Map
import Control.Monad.Reader
import Data.Char
import Data.Tree

import MPCL(StdCoord(..), dummyStdCoord)
import PrettyPrinter
import TypingDefs
import HLDefs


type InterpEnv = Map.Map String HLExpr
type InterpState t = ReaderT InterpEnv IO t


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
builtinApply "_addInt#EXT" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = return $ ExprLiteral $ LitInteger (i0 + i1)
builtinApply "_subInt#EXT" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = return $ ExprLiteral $ LitInteger (i0 - i1)
builtinApply "_mulInt#EXT" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = return $ ExprLiteral $ LitInteger (i0 * i1)
builtinApply "_divInt#EXT" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = return $ ExprLiteral $ LitInteger (div i0 i1)
builtinApply "_equInt#EXT" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = return $ ExprConstructor (if i0 == i1 then "True#BI" else "False#BI") []
builtinApply "_neqInt#EXT" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = return $ ExprConstructor (if i0 /= i1 then "True#BI" else "False#BI") []
builtinApply "_leqInt#EXT" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = return $ ExprConstructor (if i0 <= i1 then "True#BI" else "False#BI") []
builtinApply "_greInt#EXT" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[])) = return $ ExprConstructor (if i0 > i1 then "True#BI" else "False#BI") []
builtinApply "_convItoC#EXT" (_, _, ExprLiteral (LitInteger i)) = return $ ExprLiteral $ LitCharacter (chr i)
builtinApply "_convCtoI#EXT" (_, _, ExprLiteral (LitCharacter c)) = return $ ExprLiteral $ LitInteger (ord c)
builtinApply "_putChr#EXT" (_, _, ExprConstructor "()2" ((_, _, ExprLiteral (LitCharacter c)):(_,_,rw):[])) = do
    lift $ putChar c
    return rw
builtinApply "_getChr#EXT" rw@(c,_,_) = do
    lift $ hFlush stdout
    char <- lift getChar
    return $ ExprConstructor "()2" [(c, DataTypeName "Chr#BI" KType, ExprLiteral $ LitCharacter char),rw]

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
        (c, myt, myf) -> error $ show c ++ " WHAT: " ++ show myf ++ " : " ++ show myt
eval e@(c, dt, ExprLabel l) = do
    env <- ask
    case Map.lookup l env of
        Just expr -> eval expr
        Nothing -> return e
eval e@(c, dt, ExprConstructor l es) = do
    es' <- mapM eval es
    return (c, dt, ExprConstructor l es')
eval e@(_, _, ExprLambda _ _) = return e
eval e@(c, dt, ExprPut val pses) = do
    val' <- eval val
    choosePattern c val' pses

evalProgram :: (HLExpr, [(String, HLExpr)]) -> IO HLExpr
evalProgram (entryPoint, defs) = do
    let env = Map.fromList defs
    putStrLn $ "\n---- ESEGUO IL PROGRAMMA ----"
    runReaderT (eval entryPoint) env
    --TODO: così main può avere soltanto il tipo: (), il che non viene controllato nel typer
