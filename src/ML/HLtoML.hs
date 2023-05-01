module ML.HLtoML(hltoml) where
import Parser.MPCL(StdCoord)
import CompDefs
import Typer.TypingDefs
import HLDefs
import MLDefs
import ML.MLOps
import Control.Monad.State

--TODO posso usare una hlexpr subst, questo potrebbe aiutarmi nel ristrutturare il tutto per compilare più test sulla stessa cosa insieme
pushvalassigns :: [([(String, HLPattern)], MLExpr)] -> [([(String, HLPattern)], MLExpr)]
pushvalassigns = map (uncurry $ pushvals [])
    where pushvals ps [] e = (ps, e)
          pushvals ps ((l,(c, pt, ml, pd)):lps) e =
              let ps' = case pd of
                    PatWildcard -> ps
                    _ -> (l, (c, pt, Nothing, pd)) : ps
                  e' = case ml of
                      Nothing -> e
                      Just patlab -> mllabsubst patlab l e
              in pushvals ps' lps e'

chooseTestHeuristic :: [([(String, HLPattern)], MLExpr)] -> MLState (StdCoord, String, DataType, MLPattern)
chooseTestHeuristic ((lps,_):lpsses) = 
    let occurences = map (\(l, p) -> ((l,p), length $ filter (any ((l ==) . fst) . fst) lpsses)) lps in
    case fst $ maximumOn snd occurences of
    (lab, (c, pt, _, PatLiteral lit)) -> return (c, lab, pt, MLPLiteral lit)
    (lab, (c, pt, _, PatVariant var subps)) -> do
        newlabs <- mapM (\(_,mypt,_,_)-> (\pl -> (pl, mypt)) <$> newlab) subps
        return (c, lab, pt, MLPVariant var newlabs)
    where maximumOn f = foldr1 (\a b -> if f a < f b then b else a)

patCompatibility :: MLPattern -> HLPattern -> Maybe [(String, HLPattern)]
patCompatibility (MLPLiteral l) (_,_,_, PatLiteral l') = if l == l' then Just [] else Nothing
patCompatibility (MLPVariant v ls) (_,_,_, PatVariant v' ps) = if v == v' then Just $ zipWith (\myl myp -> (fst myl, myp)) ls ps else Nothing

splitTests :: String -> MLPattern -> [([(String, HLPattern)], MLExpr)] -> ([([(String, HLPattern)], MLExpr)], [([(String, HLPattern)], MLExpr)])
splitTests lab pat = inner [] []
  where inner pos neg [] = (pos, neg)
        inner pos neg (lpse@(lps, e):lpsses) =
            case lookup lab lps of
                Nothing -> inner (pos++[lpse]) (neg++[lpse]) lpsses
                Just hlpat -> case patCompatibility pat hlpat of
                    Nothing -> inner pos (neg++[lpse]) lpsses
                    Just subtests -> inner (pos ++ [(subtests ++ filter ((lab /=) . fst) lps, e)]) neg lpsses

treatput :: StdCoord -> DataType -> [([(String, HLPattern)], MLExpr)] -> MLState MLExpr
treatput c t [] = return (c, t, MLError c "Pattern matching failure")
treatput c t lpsses = do
    let lpsses' = pushvalassigns lpsses
    if null $ fst $ head lpsses' then return $ snd $ head lpsses'
    else do
        (testc, testlab, testty, testpat) <- chooseTestHeuristic lpsses'
        lift $ compLog $ show testc ++ " TEST PATTERN:" ++ show testpat
        let (positive, negative) = splitTests testlab testpat lpsses'
        lift $ compLog $ show c ++ " COMPILING TESTS:" ++ show positive ++ show negative
        mlpos <- treatput testc t positive
        mlneg <- treatput testc t negative
        return (c, t, MLTest testlab testty testpat mlpos mlneg)

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
    where combtodef (labl, il, args, myexpr) = do
            mlexpr <- exprtomlexpr myexpr
            return (labl, args, mlexpr)
