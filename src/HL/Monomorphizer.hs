module HL.Monomorphizer (monomorphizeProgram) where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List(find, partition)
import Data.Maybe(isJust, catMaybes)
import Control.Monad.State

import CompDefs
import HLDefs
import Parser.MPCL(dummyStdCoord)
import Typer.TypingDefs
import Typer.MGUs
import Typer.TypeTyper(substApplyExpr)

type Instances = [(DataType, String)]
type Generators = [(DataType, HLExpr)]

type MonoEnv = (Int, [Combinator], Map.Map String (Instances, Generators))
type MonoState t = StateT MonoEnv CompMon t

monoLog :: String -> MonoState ()
monoLog = lift . compLog

addDef :: String -> HLExpr -> MonoState ()
addDef l e = do
    (u, defs, env) <- get
    put (u, (l, False, [], e) : defs, env)
getInsts :: String -> MonoState Instances
getInsts l = do
    (_, _, e) <- get
    let Just (is, _) = Map.lookup l e
    return is
addInst :: String -> DataType -> String -> MonoState ()
addInst l t l' = do
    (u, defs, e) <- get
    let Just (is, gs) = Map.lookup l e
        e' = Map.insert l ((t, l'):is, gs) e
    put (u, defs, e')
getGenerators :: String -> MonoState Generators
getGenerators l = do
    (_, _, e) <- get
    let Just (_, gs) = Map.lookup l e
    return gs
newMonoSuffix :: MonoState String
newMonoSuffix = do
    (u, defs, e) <- get
    put (u+1, defs, e)
    return ('#':show u)
isGlobal :: String -> MonoState Bool
isGlobal l = do
    (_, _, e) <- get
    return $ isJust $ Map.lookup l e

findGenerator :: String -> DataType -> Generators -> Maybe HLExpr
findGenerator l t = getMostSpecific
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
                [] -> error $ "No matching generators of: " ++ show l ++ " with type: " ++ show t ++ "\nAvailable gens: " ++ show tses
                [(te, e)] -> do
                    s <- match dummyStdCoord te t
                    Just (substApplyExpr s e)
                xs -> error $ "Cannot find most specific instance of: " ++ show l ++ " with type: " ++ show t ++ "\n    Possible instances are: " ++ show (map fst xs)

generateInstance :: String -> DataType -> MonoState String
generateInstance l t = do
    gs <- getGenerators l
    let Just e = findGenerator l t gs
    s <- newMonoSuffix
    addInst l t (l++s)
    e' <- monomorphize s e
    addDef (l++s) e'
    return (l++s)

findInstance :: String -> DataType -> MonoState String
findInstance l t =  if (not . null) (freetyvars t) then error "WHAT: there are free type variables in instance search" else do
    monoLog $ "Looking for instance of: " ++ show l ++ " with type: " ++ show t
    is <- getInsts l
    case find ((==) t . fst) is of
        Just (_, l') -> do
            monoLog $ "Instance found: " ++ show l'
            return l'
        Nothing -> do
            monoLog "Instance not found, generating..."
            generateInstance l t

monomorphizePatInner :: String -> HLPatternData -> MonoState HLPatternData
monomorphizePatInner _ PatWildcard = return PatWildcard
monomorphizePatInner _ p@(PatLiteral _) = return p
monomorphizePatInner s (PatVariant c ps) = do
    ps' <- mapM (monomorphizePat s) ps
    return (PatVariant c ps')
    --TODO: In futuro trova i data giusti

monomorphizePat :: String -> HLPattern -> MonoState HLPattern
monomorphizePat s (c, ml, i) = do
    i' <- monomorphizePatInner s i
    return (c, fmap (++s) ml, i')

monomorphizeInner :: DataType -> String -> HLExprData -> MonoState HLExprData
monomorphizeInner _ _ e@(ExprLiteral _) = return e
monomorphizeInner _ s (ExprApp f a) = do
    f' <- monomorphize s f
    a' <- monomorphize s a
    return (ExprApp f' a')
monomorphizeInner t s (ExprLabel l) = do
    isglob <- isGlobal l
    if isglob then do
        l' <- findInstance l t
        return (ExprCombinator l' [])
    else return (ExprLabel (l++s))
monomorphizeInner _ s (ExprConstructor c es) = do
    es' <- mapM (monomorphize s) es
    return (ExprConstructor c es')
monomorphizeInner _ s (ExprCombinator l es) = do
    es' <- mapM (monomorphize s) es
    return (ExprCombinator l es')
monomorphizeInner _ s (ExprLambda l e) = do
    e' <- monomorphize s e
    return (ExprLambda (l++s) e')
monomorphizeInner _ s (ExprPut vs pses) = do
    vs' <- mapM (monomorphize s) vs
    pses' <- mapM (\(ps, e) -> do {ps' <- mapM (monomorphizePat s) ps; e' <- monomorphize s e; return (ps', e')}) pses
    return (ExprPut vs' pses')
monomorphizeInner t s (ExprHint _ e) = do
    e' <- monomorphize s e
    return (ExprHint t e')

monomorphize :: String -> HLExpr -> MonoState HLExpr
monomorphize s e@(c, t, _) = do
    let monoSubst = Map.fromList $ map (\q -> (q, buildTupType [])) $ Set.toList (freetyvars t)
        (_, t', ed) = substApplyExpr monoSubst e
    ed' <- monomorphizeInner t' s ed
    return (c, t', ed')

myListMerge :: Eq k => [(k,v)]->[(k,[v])]
myListMerge [] = []
myListMerge ((k,v):kvs) =
    let (isk, isntk) = partition ((k==) . fst) kvs
        in (k, v:map snd isk):myListMerge isntk

monomorphizeProgram :: (HLExpr, BlockProgram) -> CompMon MonoProgram
monomorphizeProgram (entryPoint, BlockProgram datagroups extdefs reldefs valgroups instdefs) =
    let
        valbinds = join valgroups
        valVtables = map (\(ValDef _ l _ _ e@(_, t, _))->(l, [(t, e)])) valbinds
        instsList = myListMerge $ map (\(InstDef _ (Qual _ (Pred l _)) cles) -> (l, cles)) instdefs
        instsListTEs = map (\(il, cless) -> (il, map (\(c, l, e@(_, t, _))->(l, (t, e))) (concat cless))) instsList
        instsVtables :: [(String, [(DataType, HLExpr)])]
        instsVtables = concatMap (myListMerge . snd) instsListTEs

        env = Map.fromList $ map (\(l, tses) -> (l, ([], tses))) (valVtables ++ instsVtables)
    in do
        (entryPoint', (_, defs, _)) <- runStateT (monomorphize "" entryPoint) (0, [], env)
        return (entryPoint', defs)
    --TODO: così main può avere soltanto il tipo: (), il che non viene controllato nel typer
