module PrettyPrinter where
import Data.Tree
import HLDefs
import SyntaxDefs

--Roba per HL
toTreeHLPattern p = Node (show p) []

toTreeHLExpr (c, dt, ExprLiteral l) = Node (show c ++ " DT:" ++ show dt ++ " Literal: " ++ show l) []
toTreeHLExpr (c, dt, ExprApp f a) = Node (show c ++ " DT:" ++ show dt ++ " Function call") [toTreeHLExpr f, toTreeHLExpr a]
toTreeHLExpr (c, dt, ExprLabel l) = Node (show c ++ " DT:" ++ show dt ++ " Label: " ++ show l) []
toTreeHLExpr (c, dt, ExprConstructor l es) = Node (show c ++ " DT:" ++ show dt ++ " Constructor: " ++ show l) (map toTreeHLExpr es)
--toTreeHLExpr (c, dt, ExprTuple es) = Node (show c ++ " DT:" ++ show dt ++ " Tuple") (map toTreeHLExpr es)
toTreeHLExpr (c, dt, ExprLambda p expr) = Node (show c ++ " DT:" ++ show dt ++ " Lambda") [Node "arg" [toTreeHLPattern p], Node "expr" [toTreeHLExpr expr]]
toTreeHLExpr (c, dt, ExprPut val branches) = Node (show c ++ " DT:" ++ show dt ++ " Put") [Node "val" [toTreeHLExpr val], Node "branches" (map (\(p, e) -> Node "branch" [Node "pat" [toTreeHLPattern p], Node "expr" [toTreeHLExpr e]]) branches)]

toTreeHLValDef (ValDef c s e) = Node (show c ++ " Defining val: " ++ show s) [toTreeHLExpr e]

--Roba per Syn
toTreeSynPattern p = Node (show p) []

toTreeSynExpr (c, SynExprLiteral l) = Node (show c ++ " Literal: " ++ show l) []
toTreeSynExpr (c, SynExprApp f a) = Node (show c ++ " Function call") [toTreeSynExpr f, toTreeSynExpr a]
toTreeSynExpr (c, SynExprLabel l) = Node (show c ++ " Label: " ++ show l) []
toTreeSynExpr (c, SynExprConstructor l) = Node (show c ++ " Constructor: " ++ show l) []
toTreeSynExpr (c, SynExprTuple es) = Node (show c ++ " Tuple") (map toTreeSynExpr es)
toTreeSynExpr (c, SynExprLambda p expr) = Node (show c ++ " Lambda") [Node "arg" [toTreeSynPattern p], Node "expr" [toTreeSynExpr expr]]
toTreeSynExpr (c, SynExprPut val branches) = Node (show c ++ " Put") [Node "val" [toTreeSynExpr val], Node "branches" (map (\(p, e) -> Node "branch" [Node "pat" [toTreeSynPattern p], Node "expr" [toTreeSynExpr e]]) branches)]


toTreeSynValDef (SynValDef c v s e) = Node (show c ++ " Defining " ++ show v ++ " val: " ++ show s) [toTreeSynExpr e]

toTreeSynTypeExpr :: SyntaxTypeExpr -> Tree String
toTreeSynTypeExpr te = Node (show te) []

toTreeSynDataVariant (DataVariant c labl args) = Node (show c ++ " DataVariant: " ++ show labl) (map (\(dt, te) -> Node "arg" [Node (show dt) [], toTreeSynTypeExpr te]) args)

toTreeSynDataDef (DataDef c v labl quants variants) = Node (show c ++ " Defining " ++ show v ++ " data: " ++ show labl ++ " with quantifiers: " ++ show quants)
    (map toTreeSynDataVariant variants)

toTreeBlockProgram (BlockProgram valgroups) = Node "BlockProgram" [
        Node "Vals" (map (\group->Node "Group of vals" (map toTreeHLValDef group)) valgroups)
    ]

toTreeSynModDef (ModMod c v l m) = Node (show c ++ " Defining " ++ show v ++ " module: " ++ show l) [toTreeSynMod m]
toTreeSynModDef (ModUse c v p) = Node (show c ++ " Using " ++ show v ++ " module: " ++ show p) []
toTreeSynModDef (ModValGroup vvdefs) = Node "Group of vals" (map toTreeSynValDef vvdefs)
toTreeSynModDef (ModDataGroup group) = Node "Group of datas" (map toTreeSynDataDef group)

toTreeSynMod (Module defs) = Node "Module" (map toTreeSynModDef defs)
