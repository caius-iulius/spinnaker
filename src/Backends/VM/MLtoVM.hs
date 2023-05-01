module Backends.VM.MLtoVM (progToVm) where
import Data.List(elemIndex)

import MLDefs
import Backends.VM.VM

patToVm :: MLPattern -> ([String], VMPat)
patToVm (MLPLiteral lit) = ([], PConst lit)
patToVm (MLPVariant v ls) = (map fst ls, PVariant v)

exprToVm :: [String] -> MLExpr -> VMCode
exprToVm _ (_, _, MLLiteral lit) = [IConst lit]
exprToVm vs (_, _, MLLabel l) =
    case elemIndex l vs of
        Just i -> [IAccess i]
exprToVm vs (_, _, MLConstructor v es) =
    (es >>= exprToVm vs) ++ [IVariant v (length es)]
exprToVm vs (_, _, MLCombinator l es) =
    (es >>= exprToVm vs) ++ [ICombApp l (length es)]
exprToVm vs (_, _, MLTest l _ pes def) =
    let v = case elemIndex l vs of
                Just i -> IAccess i
                Nothing -> error $ "WHAT " ++ show l ++ show vs
        pcs = map (\(p, e) ->
            let (ls, p') = patToVm p
                in (p', exprToVm (reverse ls ++ vs) e ++ [IRet])) pes
        cdef = exprToVm vs def ++ [IRet]
    in [v, ITest pcs cdef]
exprToVm vs (_, _, MLLet l e0 e1) = exprToVm vs e0 ++ [ILet] ++ exprToVm (l:vs) e1 ++ [IUnlet]
exprToVm vs (_, _, MLError c s) = [IError (show c ++ s)]

combToVm :: MLDef -> (Name, VMCode)
combToVm (l, as, e) = (l, exprToVm (reverse $ map fst as) e ++ [IRet])

progToVm :: MLProgram -> (VMCode, [(Name, VMCode)])
progToVm (ep, defs) =
    let cep = exprToVm [] ep ++ [IRet]
        cdefs = map combToVm defs
    in (cep, cdefs)
