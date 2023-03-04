module VM.MLtoVM (progToVm) where
import Data.List(elemIndex)
import Data.Maybe(fromMaybe)

import MLDefs
import VM.VM

patToVm (MLPLiteral lit) = ([], PConst lit)
patToVm (MLPVariant v ls) = (ls, PVariant v)

exprToVm :: [String] -> MLExpr -> VMCode
exprToVm _ (_, _, MLLiteral lit) = [IConst lit]
exprToVm vs (_, _, MLLabel l) =
    case elemIndex l vs of
        Just i -> [IAccess i]
exprToVm vs (_, _, MLConstructor v es) =
    (es >>= exprToVm vs) ++ [IVariant v (length es)]
exprToVm vs (_, _, MLCombinator l es) =
    (es >>= exprToVm vs) ++ [ICombApp l (length es)]
exprToVm vs (_, _, MLTest l p epos eneg) =
    let v = case elemIndex l vs of
                Just i -> IAccess i
                Nothing -> error $ "WHAT " ++ show l ++ show vs
        (ls, p') = patToVm p
        cpos = exprToVm (reverse ls ++ vs) epos ++ [IRet]
        cneg = exprToVm vs eneg ++ [IRet]
    in [v, ITest p' cpos cneg]
exprToVm vs (_, _, MLLet l e0 e1) = exprToVm vs e0 ++ [ILet] ++ exprToVm (l:vs) e1 ++ [IUnlet]
exprToVm vs (_, _, MLError c s) = [IError (show c ++ s)]

combToVm :: MLDef -> (Name, VMCode)
combToVm (l, as, e) = (l, exprToVm (reverse $ map fst as) e ++ [IRet])

progToVm :: MLProgram -> (VMCode, [(Name, VMCode)])
progToVm (ep, defs) =
    let cep = exprToVm [] ep ++ [IRet]
        cdefs = map combToVm defs
    in (cep, cdefs)
