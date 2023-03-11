module HLtoML(hltoml) where
import Parser.MPCL(StdCoord)
import CompDefs
import Typer.TypingDefs
import HLDefs
import MLDefs
import MLOps
import Control.Monad.State

type MLState t = StateT Int CompMon t

newlab :: MLState String
newlab = do
    uid <- get
    put (uid + 1)
    return ("_ml#" ++ show uid)

pushvalassigns = map (uncurry $ pushvals [])
    where pushvals ps [] e = (ps, e)
          pushvals ps ((l,(c, ml, pd)):lps) e =
              let ps' = case pd of
                    PatWildcard -> ps
                    _ -> (l, (c, Nothing, pd)) : ps
              in let e' = case ml of
                      Nothing -> e
                      Just patlab -> mllabsubst patlab l e
              in pushvals ps' lps e'

chooseTestHeuristic ((lps,_):lpsses) = 
    let occurences = map (\(l, p) -> ((l,p), length $ filter (any ((l ==) . fst) . fst) lpsses)) lps in
    case fst $ maximumOn snd occurences of
    (lab, (c, _, PatLiteral lit)) -> return (c, (lab, MLPLiteral lit))
    (lab, (c, _, PatVariant var subps)) -> do
        newlabs <- mapM (const newlab) [1..length subps]
        return (c, (lab, MLPVariant var newlabs))
    where maximumOn f = foldr1 (\a b -> if f a < f b then b else a)

patCompatibility (MLPLiteral l) (_,_, PatLiteral l') = if l == l' then Just [] else Nothing
patCompatibility (MLPVariant v ls) (_,_, PatVariant v' ps) = if v == v' then Just $ zip ls ps else Nothing

splitTests (lab, pat) = inner [] []
  where inner pos neg [] = (pos, neg)
        inner pos neg (plse@(pls, e):plsses) =
            case lookup lab pls of
                Nothing -> inner (pos++[plse]) (neg++[plse]) plsses
                Just hlpat -> case patCompatibility pat hlpat of
                    Nothing -> inner pos (neg++[plse]) plsses
                    Just subtests -> inner (pos ++ [(subtests ++ filter ((lab /=) . fst) pls, e)]) neg plsses

treatput :: StdCoord -> DataType -> [([(String, HLPattern)], MLExpr)] -> MLState MLExpr
treatput c t [] = return (c, t, MLError c "Pattern matching failure")
treatput c t plsses = do
    let plsses' = pushvalassigns plsses
    if null $ fst $ head plsses' then return $ snd $ head plsses'
    else do
        (patc, testpat) <- chooseTestHeuristic plsses'
        lift $ compLog $ show patc ++ " TEST PATTERN:" ++ show testpat
        let (positive, negative) = splitTests testpat plsses'
        lift $ compLog $ show c ++ " COMPILING TESTS:" ++ show positive ++ show negative
        mlpos <- treatput patc t positive
        mlneg <- treatput patc t negative
        return (c, t, uncurry MLTest testpat mlpos mlneg)

exprtomlexpr :: HLExpr -> MLState MLExpr
exprtomlexpr (c, t, ExprLiteral l) = return (c, t,MLLiteral l)
exprtomlexpr (c, t, ExprLabel l) = return (c, t, MLLabel l)
exprtomlexpr (c, t, ExprConstructor v es) = do
    mles <- mapM exprtomlexpr es
    return (c, t, MLConstructor v mles)
exprtomlexpr (c, t, ExprCombinator cmb es) = do
    mles <- mapM exprtomlexpr es
    return (c, t, MLCombinator cmb mles)
exprtomlexpr (c, t, ExprPut es psses) = do
    mles <- mapM exprtomlexpr es
    ls <- mapM (const newlab) [1..length es]
    mergedlps_etoml <- mapM (\(ps, e) -> do
            mle <- exprtomlexpr e --TODO: metti label qui per evitare duplicazione, oppure crea combinatori nello step precedente
            return (zip ls ps, mle)) psses
    mlmatch <- treatput c t mergedlps_etoml
    return $ foldr (\(l, e) e' -> (c, t, MLLet l e e')) mlmatch $ zip ls mles

hltoml :: MonoProgram -> Int -> CompMon (MLProgram, Int)
hltoml (expr, combs) uid = flip runStateT uid $ do
    mlexpr <- exprtomlexpr expr
    defs <- mapM combtodef combs
    return (mlexpr, defs)
        where combtodef (labl, il, args, expr) = do
                mlexpr <- exprtomlexpr expr
                return (labl, args, mlexpr)
