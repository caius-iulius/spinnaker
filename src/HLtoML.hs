module HLtoML(hltoml) where
import Parser.MPCL(StdCoord)
import Typer.TypingDefs
import HLDefs
import MLDefs
import Control.Monad.State

mllabsubst l l' (c, t, mled) = (c, t, inner mled)
    where
        inner (MLLiteral l) = MLLiteral l
        inner (MLLabel myl) = if myl == l then MLLabel l' else MLLabel myl
        inner (MLConstructor v es) = MLConstructor v $ map (mllabsubst l l') es
        inner (MLCombinator cmb es) = MLCombinator cmb $ map (mllabsubst l l') es
        inner (MLTest tl p e0 e1) = MLTest (if tl == l then l' else tl) p (mllabsubst l l' e0) (mllabsubst l l' e1)
        inner (MLLet ll e0 e1) = MLLet ll (mllabsubst l l' e0) (mllabsubst l l' e1)
        inner (MLError c s) = MLError c s

simplifylets (c, t, MLLiteral l) = (c, t, MLLiteral l)
simplifylets (c, t, MLLabel l) = (c, t, MLLabel l)
simplifylets (c, t, MLConstructor v es) = (c, t, MLConstructor v $ map simplifylets es)
simplifylets (c, t, MLCombinator v es) = (c, t, MLCombinator v $ map simplifylets es)
simplifylets (c, t, MLTest l p e0 e1) = (c, t, MLTest l p (simplifylets e0) (simplifylets e1))
simplifylets (c, t, MLLet l (_, _, MLLabel l') e1) = mllabsubst l l' $ simplifylets e1
simplifylets (c, t, MLLet l e0 e1) = (c, t, MLLet l (simplifylets e0) (simplifylets e1))
simplifylets (c, t, MLError c' s) = (c, t, MLError c' s)

type MLState t = StateT Int IO t

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

hltoml :: MonoProgram -> Int -> IO (MLProgram, Int)
hltoml (expr, combs) uid = flip runStateT uid $ do
    mlexpr <- exprtomlexpr expr
    defs <- mapM combtodef combs
    return (simplifylets mlexpr, defs)
        where combtodef (labl, il, args, expr) = do
                mlexpr <- exprtomlexpr expr
                return (labl, args, simplifylets mlexpr)
