module ML.MLOps where
import Data.List(union)
import Control.Monad.State
import CompDefs
import MLDefs

type MLState t = StateT Int CompMon t
runMLState :: MLState t -> Int -> CompMon (t, Int)
runMLState = runStateT

newlab :: MLState String
newlab = do
    uid <- get
    put (uid + 1)
    return ("_ml#" ++ show uid)

mlexprSize :: MLExpr -> Int
mlexprSize (_, _, MLLiteral _) = 1
mlexprSize (_, _, MLLabel _) = 1
mlexprSize (_, _, MLConstructor _ es) = 1 + sum (map mlexprSize es)
mlexprSize (_, _, MLCombinator _ es) = 1 + sum (map mlexprSize es)
mlexprSize (_, _, MLTest _ _ pes def) = 2 + sum (map (mlexprSize . snd) pes) + mlexprSize def
mlexprSize (_, _, MLProj _ _ _ _) = 1
mlexprSize (_, _, MLLet _ e0 e1) = 1 + mlexprSize e0 + mlexprSize e1
mlexprSize (_, _, MLError _ _) = 1

mlappears :: String -> MLExpr -> Int
mlappears l (_, _, MLLiteral _) = 0
mlappears l (_, _, MLLabel l') = if l == l' then 1 else 0
mlappears l (_, _, MLConstructor _ es) = sum (map (mlappears l) es)
mlappears l (_, _, MLCombinator _ es) = sum (map (mlappears l) es)
mlappears l (_, _, MLTest l' _ pes def) = (if l == l' then 1 else 0) + sum (map (mlappears l . snd) pes) + mlappears l def
mlappears l (_, _, MLProj l' _ _ _) = if l == l' then 1 else 0
mlappears l (_, _, MLLet l' e0 e1) = mlappears l e0 + (if l == l' then 0 else mlappears l e1)
mlappears l (_, _, MLError _ _) = 0

mlprogramSize :: MLProgram -> Int
mlprogramSize (ep, defs) = mlexprSize ep + sum (map (mlexprSize . (\(_,_,a)->a)) defs)

mllabsubst :: String -> String -> MLExpr -> MLExpr
mllabsubst l l' (c, t, mled) = (c, t, inner mled)
    where
        inner (MLLiteral lit) = MLLiteral lit
        inner (MLLabel myl) = if myl == l then MLLabel l' else MLLabel myl
        inner (MLConstructor v es) = MLConstructor v $ map (mllabsubst l l') es
        inner (MLCombinator cmb es) = MLCombinator cmb $ map (mllabsubst l l') es
        inner (MLTest tl ty pes def) = MLTest (if tl == l then l' else tl) ty (map (\(myp, mye) -> (myp, mllabsubst l l' mye)) pes) (mllabsubst l l' def)
        inner (MLProj dl ty var n) = MLProj (if dl == l then l' else dl) ty var n
        inner (MLLet ll e0 e1) = MLLet ll (mllabsubst l l' e0) (mllabsubst l l' e1)
        inner (MLError myc s) = MLError myc s

unions :: Eq a => [[a]] -> [a]
unions = foldr union []
--TODO: specializza a tipi?
variantsUsed :: MLExpr -> [String]
variantsUsed (_, _, MLLiteral _) = []
variantsUsed (_, _, MLLabel _) = []
variantsUsed (_, _, MLConstructor v es) = unions $ [v]:map variantsUsed es
variantsUsed (_, _, MLCombinator _ es) = unions $ map variantsUsed es
variantsUsed (_, _, MLTest _ _ pes def) = unions $ variantsUsed def : map (\(p, e) -> union (patvar p) (variantsUsed e)) pes
    where patvar p = case p of
            MLPVariant pl -> [pl]
            _ -> []
variantsUsed (_, _, MLProj _ ty var _) = [var]
variantsUsed (_, _, MLLet _ e0 e1) = union (variantsUsed e0) (variantsUsed e1)
variantsUsed (_, _, MLError _ _) = []

variantsUsedProg :: MLProgram -> [String]
variantsUsedProg (ep, defs) =
    unions $ variantsUsed ep : map variantsUsedDef defs
    where variantsUsedDef (_, _, e) = variantsUsed e
