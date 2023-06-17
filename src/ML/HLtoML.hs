module ML.HLtoML(hltoml) where
import Parser.MPCL(StdCoord)
import CompDefs
import Typer.TypingDefs
import HLDefs
import MLDefs
import ML.MLOps
import Control.Monad.State

type Branches = [([(String, HLPattern)], MLExpr)]
pushvalassigns :: Branches -> Branches
pushvalassigns = map (uncurry $ pushvals [])
    where pushvals ps [] e = (ps, e)
          pushvals ps ((l,(c, pt, ml, pd)):lps) e =
              let ps' = case pd of
                    PatWildcard -> ps
                    _ -> (l, (c, pt, Nothing, pd)) : ps
                  e' = case ml of
                      Nothing -> e
                      Just patlab -> mlsubst patlab (c, pt, MLLabel l) e
              in pushvals ps' lps e'

chooseTestHeuristic :: Branches -> (StdCoord, DataType, String)
chooseTestHeuristic ((lps,_):lpsses) = 
    let occurences = map (\(l, p) -> ((l,p), length $ filter (any ((l ==) . fst) . fst) lpsses)) lps
        (lab, (c, pt, _, _)) = fst $ maximumOn snd occurences
    in (c, pt, lab)
    where maximumOn f = foldr1 (\a b -> if f a < f b then b else a)

patCompatibility :: (MLPattern, [(String, DataType)]) -> HLPattern -> Maybe [(String, HLPattern)]
patCompatibility (MLPLiteral l, []) (_,_,_, PatLiteral l') = if l == l' then Just [] else Nothing
patCompatibility (MLPVariant v, ls) (_,_,_, PatVariant v' ps) = if v == v' then Just $ zipWith (\myl myp -> (fst myl, myp)) ls ps else Nothing

pattomlpat :: HLPattern -> MLState (MLPattern, [(String, DataType)])
pattomlpat (c, pt, _, PatLiteral lit) = return (MLPLiteral lit, [])
pattomlpat (c, pt, _, PatVariant var subps) = do
    ls <- mapM (\(_,mypt,_,_)-> (\pl -> (pl, mypt)) <$> newlab) subps
    return (MLPVariant var, ls)

appendTest :: HLPattern -> ([(String, HLPattern)], MLExpr) -> [((MLPattern, [(String, DataType)]), Branches)] -> MLState [((MLPattern, [(String, DataType)]), Branches)]
appendTest hlpat (lps, e) [] = do
    pat <- pattomlpat hlpat
    let Just subtests = patCompatibility pat hlpat
        in return [(pat, [(subtests ++ lps, e)])]
appendTest hlpat branch@(lps, e) ((p, bs) : pbs) =
    case patCompatibility p hlpat of
        Nothing -> ((p, bs) :) <$> appendTest hlpat branch pbs
        Just subtests -> return $ (p, bs ++ [(subtests ++ lps, e)]) : pbs

splitTests :: String -> Branches -> MLState ([((MLPattern, [(String, DataType)]), Branches)], Branches)
splitTests lab = inner [] []
  where inner pbs notest [] = return (pbs, notest)
        inner pbs notest (lpse@(lps, e):lpsses) =
            case lookup lab lps of
                Nothing -> inner pbs (notest++[lpse]) lpsses
                Just hlpat -> do
                    let lps' = filter ((lab /=) . fst) lps
                    pbs' <- appendTest hlpat (lps', e) pbs
                    inner pbs' notest lpsses

treatput :: StdCoord -> DataType -> Branches -> MLState MLExpr
treatput c t [] = return (c, t, MLError c "Pattern matching failure")
treatput c t lpsses = do
    let lpsses' = pushvalassigns lpsses
    if null $ fst $ head lpsses' then return $ snd $ head lpsses'
    else do
        let (testc, testty, testlab) = chooseTestHeuristic lpsses'
        lift $ compLog $ show testc ++ " TESTING LABEL:" ++ show testlab
        (test, notest) <- splitTests testlab lpsses'
        mltest <- mapM (\((pat, projs), branches) -> do
                res <- treatput c t (branches ++ notest)
                let res_projs = case pat of
                        MLPLiteral _ -> res
                        MLPVariant vname -> foldr (\(projn, (projl, projt)) e -> (c, t, MLLet projl (c, projt, MLProj (c, testty, MLLabel testlab) vname projn) e) ) res
                            $ filter (\(_, (projl, _)) -> mlappears projl res /= 0)
                            $ zip [0..] projs
                return (pat, res_projs)
            ) test
        mlnotest <- treatput testc t notest
        return (c, t, MLTest (testc, testty, MLLabel testlab)  mltest mlnotest)

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
