module ML.MLOps where
import Data.List(union)
import Control.Monad.State
import CompDefs
import MLDefs

type MLState t = StateT Int CompMon t
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
mlexprSize (_, _, MLTest _ _ _ epos eneg) = 2 + mlexprSize epos + mlexprSize eneg
mlexprSize (_, _, MLLet _ e0 e1) = 1 + mlexprSize e0 + mlexprSize e1
mlexprSize (_, _, MLError _ _) = 1

mlprogramSize (ep, defs) = mlexprSize ep + sum (map (mlexprSize . (\(_,_,a)->a)) defs)

mllabsubst l l' (c, t, mled) = (c, t, inner mled)
    where
        inner (MLLiteral l) = MLLiteral l
        inner (MLLabel myl) = if myl == l then MLLabel l' else MLLabel myl
        inner (MLConstructor v es) = MLConstructor v $ map (mllabsubst l l') es
        inner (MLCombinator cmb es) = MLCombinator cmb $ map (mllabsubst l l') es
        inner (MLTest tl ty p e0 e1) = MLTest (if tl == l then l' else tl) ty p (mllabsubst l l' e0) (mllabsubst l l' e1)
        inner (MLLet ll e0 e1) = MLLet ll (mllabsubst l l' e0) (mllabsubst l l' e1)
        inner (MLError c s) = MLError c s

unions = foldr union []
--TODO: specializza a tipi?
variantsUsed (_, _, MLLiteral _) = []
variantsUsed (_, _, MLLabel _) = []
variantsUsed (_, _, MLConstructor v es) = unions $ [(v, length es)]:map variantsUsed es
variantsUsed (_, _, MLCombinator _ es) = unions $ map variantsUsed es
variantsUsed (_, _, MLTest _ _ p pos neg) =
    let patvar = case p of
            MLPVariant p ls -> [(p, length ls)]
            _ -> []
        in union patvar $ union (variantsUsed pos) (variantsUsed neg)
variantsUsed (_, _, MLLet _ e0 e1) = union (variantsUsed e0) (variantsUsed e1)
variantsUsed (_, _, MLError _ _) = []
variantsUsedProg (ep, defs) =
    unions $ variantsUsed ep : map variantsUsedDef defs
    where variantsUsedDef (_, _, e) = variantsUsed e
