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
mlexprSize (_, _, MLJoin _ es) = 1 + sum (map mlexprSize es)
mlexprSize (_, _, MLTest tv pes def) = 1 + mlexprSize tv + sum (map (mlexprSize . snd) pes) + mlexprSize def
mlexprSize (_, _, MLProj e _ _) = 1 + mlexprSize e
mlexprSize (_, _, MLLet _ e0 e1) = 1 + mlexprSize e0 + mlexprSize e1
mlexprSize (_, _, MLLetJoin _ _ e0 e1) = mlexprSize e0 + mlexprSize e1
mlexprSize (_, _, MLError _ _) = 1

mlappears :: String -> MLExpr -> Int
mlappears l (_, _, MLLiteral _) = 0
mlappears l (_, _, MLLabel l') = if l == l' then 1 else 0
mlappears l (_, _, MLConstructor _ es) = sum (map (mlappears l) es)
mlappears l (_, _, MLCombinator _ es) = sum (map (mlappears l) es)
mlappears l (_, _, MLJoin j es) = (if l == j then 1 else 0) + sum (map (mlappears l) es)
mlappears l (_, _, MLTest tv pes def) = mlappears l tv + sum (map (mlappears l . snd) pes) + mlappears l def
mlappears l (_, _, MLProj e _ _) = mlappears l e
mlappears l (_, _, MLLet l' e0 e1) = mlappears l e0 + (if l == l' then 0 else mlappears l e1)
mlappears l (_, _, MLLetJoin j lts e0 e1) = (if elem l (map fst lts) then 0 else mlappears l e0) + (if l == j then 0 else mlappears l e1)
mlappears l (_, _, MLError _ _) = 0

mlprogramSize :: MLProgram -> Int
mlprogramSize (ep, defs) = mlexprSize ep + sum (map (mlexprSize . (\(_,_,a)->a)) defs)

mlsubst :: String -> MLExpr -> MLExpr -> MLExpr
mlsubst l e' e@(_, _, MLLiteral _) = e
mlsubst l e' e@(_, _, MLLabel myl) = if myl == l then e' else e
mlsubst l e' (c, t, MLConstructor v es) = (c, t, MLConstructor v $ map (mlsubst l e') es)
mlsubst l e' (c, t, MLCombinator cmb es) = (c, t, MLCombinator cmb $ map (mlsubst l e') es)
mlsubst l e' (c, t, MLJoin j es) = (c, t, MLJoin j $ map (mlsubst l e') es)
mlsubst l e' (c, t, MLTest tv pes def) = (c, t, MLTest (mlsubst l e' tv) (map (\(myp, mye) -> (myp, mlsubst l e' mye)) pes) (mlsubst l e' def))
mlsubst l e' (c, t, MLProj e var n) = (c, t, MLProj (mlsubst l e' e) var n)
mlsubst l e' (c, t, MLLet ll e0 e1) = (c, t, MLLet ll (mlsubst l e' e0) (mlsubst l e' e1)) --TODO: La sostituzione può avvenire solo se ll != l
mlsubst l e' (c, t, MLLetJoin j lts e0 e1) = (c, t, MLLetJoin j lts (mlsubst l e' e0) (mlsubst l e' e1))--TODO: La sostituzione può avvenire solo se l nonelem lts
mlsubst _ _ e@(_, _, MLError _ _) = e

joinsubst :: (String, [String], MLExpr) -> MLExpr -> MLExpr
joinsubst _ e@(_, _, MLLiteral _) = e
joinsubst _ e@(_, _, MLLabel _) = e
joinsubst j (c, t, MLConstructor v es) = (c, t, MLConstructor v $ map (joinsubst j) es)
joinsubst j (c, t, MLCombinator cmb es) = (c, t, MLCombinator cmb $ map (joinsubst j) es)
joinsubst (l, as, je) e@(_, _, MLJoin myl es) = if myl == l then foldl (\e' (al, ae) -> mlsubst al ae e') je (zip as es) else e
joinsubst j (c, t, MLTest tv pes def) = (c, t, MLTest (joinsubst j tv) (map (\(myp, mye) -> (myp, joinsubst j mye)) pes) (joinsubst j def))
joinsubst j (c, t, MLProj e var n) = (c, t, MLProj (joinsubst j e) var n)
joinsubst j (c, t, MLLet ll e0 e1) = (c, t, MLLet ll (joinsubst j e0) (joinsubst j e1)) --TODO: La sostituzione può avvenire solo se ll != l
joinsubst j (c, t, MLLetJoin jl lts e0 e1) = (c, t, MLLetJoin jl lts (joinsubst j e0) (joinsubst j e1))--TODO: La sostituzione può avvenire solo se j != jl
joinsubst _ e@(_, _, MLError _ _) = e

unions :: Eq a => [[a]] -> [a]
unions = foldr union []
--TODO: specializza a tipi?
variantsUsed :: MLExpr -> [String]
variantsUsed (_, _, MLLiteral _) = []
variantsUsed (_, _, MLLabel _) = []
variantsUsed (_, _, MLConstructor v es) = unions $ [v]:map variantsUsed es
variantsUsed (_, _, MLCombinator _ es) = unions $ map variantsUsed es
variantsUsed (_, _, MLJoin _ es) = unions $ map variantsUsed es
variantsUsed (_, _, MLTest tv pes def) = unions $ variantsUsed tv : variantsUsed def : map (\(p, e) -> union (patvar p) (variantsUsed e)) pes
    where patvar p = case p of
            MLPVariant pl -> [pl]
            _ -> []
variantsUsed (_, _, MLProj _ var _) = [var]
variantsUsed (_, _, MLLet _ e0 e1) = union (variantsUsed e0) (variantsUsed e1)
variantsUsed (_, _, MLLetJoin _ _ e0 e1) = union (variantsUsed e0) (variantsUsed e1)
variantsUsed (_, _, MLError _ _) = []

variantsUsedProg :: MLProgram -> [String]
variantsUsedProg (ep, defs) =
    unions $ variantsUsed ep : map variantsUsedDef defs
    where variantsUsedDef (_, _, e) = variantsUsed e
