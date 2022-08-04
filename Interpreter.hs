module Interpreter where
import System.IO(hFlush, stdout)
import System.Exit(exitSuccess)
import Control.Monad.Reader
import Data.Char(ord, chr)
import Data.Tree(drawTree)

import MPCL(StdCoord(..), dummyStdCoord)
import PrettyPrinter(toTreeHLExpr)
import TypingDefs
import HLDefs


type InterpBinds = [(String, HLExpr)]
type InterpState t = ReaderT InterpBinds IO t


sievePatternInner :: HLPatternData -> HLExpr -> Maybe InterpBinds
sievePatternInner PatWildcard _ = return []
sievePatternInner (PatLiteral plit) (_, _, ExprLiteral elit) =
    if plit == elit then return [] else Nothing
sievePatternInner (PatVariant pvar ps) (_, _, ExprConstructor evar es) =
    if pvar == evar then do
        maps <- zipWithM sievePattern ps es
        return $ concat maps
    else Nothing
sievePatternInner p e = error $ show p ++ " : \n\n" ++ (drawTree $ toTreeHLExpr e)

sievePattern :: HLPattern -> HLExpr -> Maybe InterpBinds
sievePattern (_, Nothing, patdata) e = sievePatternInner patdata e
sievePattern (_, Just l, patdata) e = do
    inner <- sievePatternInner patdata e
    return $ (l,e):inner

getBindsInner :: HLPatternData -> [String]
getBindsInner PatWildcard = []
getBindsInner (PatLiteral _) = []
getBindsInner (PatVariant _ ps) = join $ map getBinds ps

getBinds :: HLPattern -> [String]
getBinds (_, Nothing, patdata) = getBindsInner patdata
getBinds (_, Just l, patdata) = l : getBindsInner patdata

mapDelete k [] = []
mapDelete k ((mk,mv):kvs)
    | k == mk = mapDelete k kvs
    | otherwise = (mk,mv) : mapDelete k kvs

exprSubstApply :: InterpBinds -> HLExpr -> HLExpr
exprSubstApply _ e@(_, _, ExprLiteral _) = e
exprSubstApply s (c, dt, ExprApp e0 e1) = (c, dt, ExprApp (exprSubstApply s e0) (exprSubstApply s e1))
exprSubstApply s e@(_, _, ExprLabel l) =
    case lookup l s of
        Nothing -> e
        Just expr -> expr
exprSubstApply s (c, dt, ExprConstructor v es) = (c, dt, ExprConstructor v (map (exprSubstApply s) es))
exprSubstApply s (c, dt, ExprCombinator v es) = (c, dt, ExprCombinator v (map (exprSubstApply s) es))
exprSubstApply s (c, dt, ExprLambda pat ret) =
    let
        s' = foldl (flip mapDelete) s (getBinds pat)
    in (c, dt, ExprLambda pat (exprSubstApply s' ret))
exprSubstApply s (c, dt, ExprPut val pses) =
    let
        peSubstApply (p, e) = (p, exprSubstApply (foldl (flip mapDelete) s (getBinds p)) e)
    in (c, dt, ExprPut (exprSubstApply s val) (map peSubstApply pses))

builtinApply :: String -> [HLExpr] -> InterpState HLExprData
builtinApply "_addInt" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[]) = return $ ExprLiteral $ LitInteger (i0 + i1)
builtinApply "_subInt" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[]) = return $ ExprLiteral $ LitInteger (i0 - i1)
builtinApply "_mulInt" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[]) = return $ ExprLiteral $ LitInteger (i0 * i1)
builtinApply "_divInt" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[]) = return $ ExprLiteral $ LitInteger (div i0 i1)
builtinApply "_equInt" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[]) = return $ ExprConstructor (if i0 == i1 then "True#BI" else "False#BI") []
builtinApply "_neqInt" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[]) = return $ ExprConstructor (if i0 /= i1 then "True#BI" else "False#BI") []
builtinApply "_leqInt" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[]) = return $ ExprConstructor (if i0 <= i1 then "True#BI" else "False#BI") []
builtinApply "_greInt" ((_, _, ExprLiteral (LitInteger i0)):(_, _, ExprLiteral (LitInteger i1)):[]) = return $ ExprConstructor (if i0 > i1 then "True#BI" else "False#BI") []
builtinApply "_convItoC" ((_, _, ExprLiteral (LitInteger i)):[]) = return $ ExprLiteral $ LitCharacter (chr i)
builtinApply "_convCtoI" ((_, _, ExprLiteral (LitCharacter c)):[]) = return $ ExprLiteral $ LitInteger (ord c)
builtinApply "_putChr" ((_, _, ExprLiteral (LitCharacter c)):(_,_,rw):[]) = do
    lift $ putChar c
    return rw
builtinApply "_getChr" (rw@(c,_,_):[]) = do
    lift $ hFlush stdout
    char <- lift getChar
    return $ ExprConstructor (makeTupLabl 2) [(c, DataTypeName "Chr#BI" KType, ExprLiteral $ LitCharacter char),rw]
builtinApply "_exit" (rw@(c,_,_):[]) = lift $ exitSuccess

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
        (_, _, ExprLambda pat ret) -> case sievePattern pat a' of
                Nothing -> error $ "WHAT SIEVE: " ++ show pat ++ " val " ++ show a'
                Just s -> eval $ exprSubstApply s ret
        (c, myt, myf) -> error $ show c ++ " WHAT: " ++ show myf ++ " : " ++ show myt
eval e@(c, dt, ExprLabel l) = do
    env <- ask
    let Just expr = lookup l env in eval expr
eval e@(c, dt, ExprConstructor l es) = do
    es' <- mapM eval es
    return (c, dt, ExprConstructor l es')
eval e@(c, dt, ExprCombinator l es) = do
    es' <- mapM eval es
    bicall <- builtinApply l es'
    return (c, dt, bicall)
eval e@(_, _, ExprLambda _ _) = return e
eval e@(c, dt, ExprPut val pses) = do
    val' <- eval val
    choosePattern c val' pses

evalProgram :: (HLExpr, [(String, HLExpr)]) -> IO HLExpr
evalProgram (entryPoint, defs) = do
    putStrLn $ "\n---- ESEGUO IL PROGRAMMA ----"
    runReaderT (eval entryPoint) defs
    --TODO: così main può avere soltanto il tipo: (), il che non viene controllato nel typer
