module HLtoVM where
import Data.List(elemIndex)
import Data.Maybe(fromMaybe)
import HLDefs
import VM

patToVmInner PatWildcard = (PWildcard, [])
patToVmInner (PatLiteral lit) = (PConst lit, [])
patToVmInner (PatVariant v ps) =
    let (ps', ls) = unzip $ map patToVm ps
        in (PVariant v ps', concat ls)

patToVm :: HLPattern -> (VMPat, [String])
patToVm (_, Nothing, ip) =
    let (ip', ls) = patToVmInner ip
        in ((False, ip'), ls)
patToVm (_, Just l, ip) =
    let (ip', ls) = patToVmInner ip
        in ((True, ip'), l:ls)

exprToVm :: [String] -> HLExpr -> VMCode
exprToVm _ (_, _, ExprLiteral lit) = [IConst lit]
exprToVm vs (_, _, ExprApp f a) = exprToVm vs f ++ exprToVm vs a ++ [IApp]
exprToVm vs (_, _, ExprLabel l) =
    case elemIndex l vs of
        Just i -> [IAccess i]
        Nothing -> [ICombApp l 0]
exprToVm vs (_, _, ExprConstructor v es) =
    (es >>= exprToVm vs) ++ [IVariant v (length es)]
exprToVm vs (_, _, ExprCombinator l es) =
    (es >>= exprToVm vs) ++ [ICombApp l (length es)]
exprToVm vs (_, _, ExprLambda (_, ml, PatWildcard) e) =
    let vs' = fromMaybe "#" ml : vs
        e' = exprToVm vs' e
    in [IClos (e' ++ [IRet])]
exprToVm vs (_, _, ExprLambda p e) =
    let (p', ls) = patToVm p
        e' = exprToVm (reverse ls ++ ["#"] ++ vs) e ++ [IRet]
    in [IClos [IAccess 0, ICase [(p',e')], IRet]]
exprToVm vs (_, _, ExprPut v pses) =
    let v' = exprToVm vs v
        pscs = map (\(p, e) ->
            let (p', ls) = patToVm p
                e' = exprToVm (reverse ls ++ vs) e ++ [IRet]
                in (p', e')
            ) pses
    in v' ++ [ICase pscs]

progToVm :: (HLExpr, [(String, HLExpr)]) -> (VMCode, [(Name, VMCode)])
progToVm (ep, defs) =
    let cep = exprToVm [] ep ++ [IRet]
        cdefs = map (fmap ((++ [IRet]) . exprToVm [])) defs
    in (cep, cdefs)
