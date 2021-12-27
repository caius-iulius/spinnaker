module PrettyPrinter where

import Data.Tree
import HIRDefs

toTreeHIRPattern :: HIRPattern -> Tree String
toTreeHIRPattern p = Node (show p) []

toTreeHIRExpr (c, dt, ExprLiteral l) = Node (show c ++ " DT:" ++ show dt ++ " Literal: " ++ show l) []
toTreeHIRExpr (c, dt, ExprFCall f a) = Node (show c ++ " DT:" ++ show dt ++ " Function call") [toTreeHIRExpr f, toTreeHIRExpr a]
toTreeHIRExpr (c, dt, ExprLabel l) = Node (show c ++ " DT:" ++ show dt ++ " Label: " ++ show l) []
toTreeHIRExpr (c, dt, ExprConstructor l) = Node (show c ++ " DT:" ++ show dt ++ " Constructor: " ++ show l) []
toTreeHIRExpr (c, dt, ExprTuple es) = Node (show c ++ " DT:" ++ show dt ++ " Tuple") (map toTreeHIRExpr es)
toTreeHIRExpr (c, dt, ExprLambda p expr) = Node (show c ++ " DT:" ++ show dt ++ " Lambda") [Node "arg" [toTreeHIRPattern p], Node "expr" [toTreeHIRExpr expr]]
toTreeHIRExpr (c, dt, ExprPut val branches) = Node (show c ++ " DT:" ++ show dt ++ " Put") [Node "val" [toTreeHIRExpr val], Node "branches" (map (\(p, e) -> Node "branch" [Node "pat" [toTreeHIRPattern p], Node "expr" [toTreeHIRExpr e]]) branches)]

toTreeHIRTypeExpr :: HIRTypeExpr -> Tree String
toTreeHIRTypeExpr te = Node (show te) []

toTreeHIRDataVariant (DataVariant c labl args) = Node (show c ++ " DataVariant: " ++ show labl) (map (\(dt, te) -> Node "arg" [Node (show dt) [], toTreeHIRTypeExpr te]) args)

toTreeHIRDataDef (DataDef c labl quants variants) = Node (show c ++ " Defining data: " ++ show labl ++ " with quantifiers: " ++ show quants)
    (map toTreeHIRDataVariant variants)

toTreeHIRValDef (ValDef c s e) = Node (show c ++ " Defining val: " ++ show s) [toTreeHIRExpr e]

toTreeHIRValDefs vdefs = Node "Group of vals" (map toTreeHIRValDef vdefs)

toTreeHIRProgram (Program ddefs vdefss) = Node "Program" [Node "Data detinitions" (map toTreeHIRDataDef ddefs), Node "Value definitions" (map toTreeHIRValDefs vdefss)]
