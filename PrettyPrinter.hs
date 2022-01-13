module PrettyPrinter where
import Data.Tree
import HLDefs
import SyntaxDefs

toTreeHLPattern p = Node (show p) []

toTreeHLExpr (c, dt, ExprLiteral l) = Node (show c ++ " DT:" ++ show dt ++ " Literal: " ++ show l) []
toTreeHLExpr (c, dt, ExprApp f a) = Node (show c ++ " DT:" ++ show dt ++ " Function call") [toTreeHLExpr f, toTreeHLExpr a]
toTreeHLExpr (c, dt, ExprLabel l) = Node (show c ++ " DT:" ++ show dt ++ " Label: " ++ show l) []
toTreeHLExpr (c, dt, ExprConstructor l) = Node (show c ++ " DT:" ++ show dt ++ " Constructor: " ++ show l) []
toTreeHLExpr (c, dt, ExprTuple es) = Node (show c ++ " DT:" ++ show dt ++ " Tuple") (map toTreeHLExpr es)
toTreeHLExpr (c, dt, ExprLambda p expr) = Node (show c ++ " DT:" ++ show dt ++ " Lambda") [Node "arg" [toTreeHLPattern p], Node "expr" [toTreeHLExpr expr]]
toTreeHLExpr (c, dt, ExprPut val branches) = Node (show c ++ " DT:" ++ show dt ++ " Put") [Node "val" [toTreeHLExpr val], Node "branches" (map (\(p, e) -> Node "branch" [Node "pat" [toTreeHLPattern p], Node "expr" [toTreeHLExpr e]]) branches)]

toTreeSyntaxTypeExpr :: SyntaxTypeExpr -> Tree String
toTreeSyntaxTypeExpr te = Node (show te) []

toTreeSyntaxDataVariant (DataVariant c labl args) = Node (show c ++ " DataVariant: " ++ show labl) (map (\(dt, te) -> Node "arg" [Node (show dt) [], toTreeSyntaxTypeExpr te]) args)

toTreeSyntaxDataDef (DataDef c v labl quants variants) = Node (show c ++ " Defining " ++ show v ++ " data: " ++ show labl ++ " with quantifiers: " ++ show quants)
    (map toTreeSyntaxDataVariant variants)

toTreeHLValDef (ValDef c s e) = Node (show c ++ " Defining val: " ++ show s) [toTreeHLExpr e]
toTreeSyntaxValDef (v, ValDef c s e) = Node (show c ++ " Defining " ++ show v ++ " val: " ++ show s) [toTreeHLExpr e]

toTreeBlockProgram (BlockProgram valgroups) = Node "BlockProgram" [
        Node "Vals" (map (\group->Node "Group of vals" (map toTreeHLValDef group)) valgroups)
    ]

toTreeSyntaxModDef (ModMod c v l m) = Node (show c ++ " Defining " ++ show v ++ " module: " ++ show l) [toTreeSyntaxMod m]
toTreeSyntaxModDef (ModUse c v p) = Node (show c ++ " Using " ++ show v ++ " module: " ++ show p) []
toTreeSyntaxModDef (ModValGroup vvdefs) = Node "Group of vals" (map toTreeSyntaxValDef vvdefs)
toTreeSyntaxModDef (ModDataGroup group) = Node "Group of datas" (map toTreeSyntaxDataDef group)

toTreeSyntaxMod (Module defs) = Node "Module" (map toTreeSyntaxModDef defs)
