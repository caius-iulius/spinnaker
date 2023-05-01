module HL.Defunctionalize (defunProgram) where
import Control.Monad.State
import Data.List(nub)

import CompDefs
import HLDefs
import HL.HLOps
import Typer.TypingDefs
import Parser.MPCL(dummyStdCoord)

type ApplysEnv = [(DataType, (String, [(String, [(String, DataType)], String)]))]
type DefunEnv = (Int, [Combinator], ApplysEnv)
type DefunState t = StateT DefunEnv CompMon t

getUid :: DefunState String
getUid = do
    (u, cs, env) <- get
    put (u+1, cs, env)
    return ('#':show u)

getApply :: DataType -> DefunState String
getApply t = do
    (u, cs, env) <- get
    case lookup t env of
        Just (l, _) -> return l
        Nothing -> do
            s <- getUid
            let combl = "_apply" ++ s
            (u', _, _) <- get
            put (u', cs, (t, (combl, [])):env)
            return combl
addApply :: DataType -> [DataType] -> String -> DefunState String
addApply t freets cmb = do
    (u, cs, env) <- get
    ((combl, brs), aps) <-
        case lookup t env of
            Just dat -> return (dat, filter ((t /=) . fst) env)
            Nothing -> do
                s <- getUid
                let combl = "_apply" ++ s
                return ((combl, []), env)
    sv <- getUid
    frees <- mapM (\ft -> fmap (\s -> ("_v" ++ s, ft)) getUid) freets
    let varl = "Lamvar_" ++ sv
        brs' = (varl, frees, cmb) : brs
    (u', _, _) <- get
    put (u', cs, (t, (combl, brs')) : aps)
    return varl

addComb :: Combinator -> DefunState ()
addComb cmb = do
    (u, cs, env) <- get
    put (u, cmb:cs, env)
newComb :: [(String, DataType)] -> HLExpr -> DefunState String
newComb as e = do
    s <- getUid
    let combl = "_comb" ++ s
    (u, cs, env) <- get
    put (u, (combl, False, as, e):cs, env)
    return combl

freeLabls :: HLExpr -> [(String, DataType)]
freeLabls (_, _, ExprLiteral _) = []
freeLabls (_, _, ExprApp f a) = nub $ freeLabls f ++ freeLabls a --TODO: le coppie labl, datatype sono sempre uguali?
freeLabls (_, t, ExprLabel l) = [(l, t)]
freeLabls (_, _, ExprConstructor l es) = nub $ es >>= freeLabls
freeLabls (_, _, ExprCombinator l es) = nub $ es >>= freeLabls
freeLabls (_, _, ExprLambda l e) = filter ((l /=) . fst) $ freeLabls e
freeLabls (_, _, ExprPut vs pses) =
    let lvss = map freeLabls vs
        lpses = map (\(ps, e) ->
            let le = freeLabls e
                in filter (\l -> not $ any (appearsPat (fst l)) ps) le
            ) pses
    in nub $ concat $ lvss ++ lpses
freeLabls (_, _, ExprHint _ e) = freeLabls e

defunExpr :: HLExpr -> DefunState HLExpr
defunExpr e@(_, _, ExprLiteral _) = return e
defunExpr e@(_, _, ExprLabel _) = return e
defunExpr (c, t, ExprApp f@(_, tf, _) a) = do
    f' <- defunExpr f
    a' <- defunExpr a
    apl <- getApply tf
    return (c, t, ExprCombinator apl [f', a'])
defunExpr (c, t, ExprConstructor l es) = do
    es' <- mapM defunExpr es
    return (c, t, ExprConstructor l es')
defunExpr (c, t, ExprCombinator l es) = do
    es' <- mapM defunExpr es
    return (c, t, ExprCombinator l es')
defunExpr le@(c, t@(DataTypeApp (DataTypeApp _ at) _), ExprLambda l e) = do
    let frees = freeLabls le
    e' <- defunExpr e
    myc <- newComb (frees ++ [(l, at)]) e'
    myv <- addApply t (map snd frees) myc
    let freerefs = map (\(myl, myt) -> (c, myt, ExprLabel myl)) frees
    return (c, t, ExprConstructor myv freerefs)
defunExpr (c, t, ExprPut vs pses) = do
    vs' <- mapM defunExpr vs
    pses' <- mapM (\(ps, e) -> fmap (\e' -> (ps, e')) (defunExpr e)) pses
    return (c, t, ExprPut vs' pses')
defunExpr (_, _, ExprHint _ e) = defunExpr e

applysToComb :: DefunState ()
applysToComb = do
    (_, _, aps) <- get
    acmbs <- mapM applyToComb aps
    (n, cmbs, _) <- get
    put (n, acmbs ++ cmbs, [])
    where applyToComb (t@(DataTypeApp (DataTypeApp _ at) rt), (combl, vars)) = do
            s <- getUid
            let funl = "_fun" ++ s
                argl = "_arg" ++ s
                vartobranch (vname, ls, cmb) =
                    ([(dummyStdCoord, t, Nothing, PatVariant vname (map (\(l,lt) -> (dummyStdCoord, lt, Just l, PatWildcard)) ls))],
                        (dummyStdCoord, rt, ExprCombinator cmb (map (\(l, lt) -> (dummyStdCoord, lt, ExprLabel l)) (ls ++ [(argl, at)]))))
            return (combl, True, [(funl, t), (argl, at)], (dummyStdCoord, rt, ExprPut [(dummyStdCoord, t, ExprLabel funl)] (map vartobranch vars)))


applysToDataSummary :: ApplysEnv -> [DataSummary]
applysToDataSummary = map summarizeApply
    where summarizeApply (dt, (_, brs)) = (dt, map summarizeBranch brs)
          summarizeBranch (varl, datalabs, _) = (varl, map snd datalabs)

defunProgram :: MonoProgram -> Int -> CompMon ([DataSummary], MonoProgram, Int)
defunProgram (ep, defs) n = do
    ((datasummary, ep'), (n', combs, _)) <- runStateT defunmon (n, [], [])
    return (datasummary, (ep', combs), n')
    where defunmon = do
            ep' <- defunExpr ep
            mapM_ (\(l, il, as, e) -> do
                e' <- defunExpr e
                addComb (l, il, as, e')
                ) defs
            (_, _, aps) <- get
            let datasummary = applysToDataSummary aps
            applysToComb
            return (datasummary, ep')
