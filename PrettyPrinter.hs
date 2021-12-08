module PrettyPrinter where

import Data.Tree
import HIRDefs

toTreeHIRPattern :: HIRPattern -> Tree String
toTreeHIRPattern p = Node (show p) []

toTreeHIRExpr (c, ExprLiteral l) = Node (show c ++ " Literal: " ++ show l) []
toTreeHIRExpr (c, ExprFCall f a) = Node (show c ++ " Function call") [toTreeHIRExpr f, toTreeHIRExpr a]
toTreeHIRExpr (c, ExprLabel l) = Node (show c ++ " Label: " ++ show l) []
toTreeHIRExpr (c, ExprTuple es) = Node (show c ++ " Tuple") (map toTreeHIRExpr es)
toTreeHIRExpr (c, ExprLambda p expr) = Node (show c ++ " Lambda") [Node "arg" [toTreeHIRPattern p], Node "expr" [toTreeHIRExpr expr]]
toTreeHIRExpr (c, ExprPut val branches) = Node (show c ++ " Put") [Node "val" [toTreeHIRExpr val], Node "branches" (map (\(p, e) -> Node "branch" [Node "pat" [toTreeHIRPattern p], Node "expr" [toTreeHIRExpr e]]) branches)]

toTreeHIRTypeExpr :: HIRTypeExpr -> Tree String
toTreeHIRTypeExpr te = Node (show te) []

toTreeHIRDataVariant (DataVariant c labl args) = Node (show c ++ " DataVariant: " ++ show labl) (map (\(dt, te) -> Node "arg" [Node (show dt) [], toTreeHIRTypeExpr te]) args)

toTreeHIRDataDef (c, DataDef labl quants variants) = Node (show c ++ " Defining data: " ++ show labl ++ " with quantifiers: " ++ show quants)
    (map toTreeHIRDataVariant variants)

toTreeProgDef (c, s, e) = Node (show c ++ " Defining: " ++ show s) [toTreeHIRExpr e]

toTreeHIRProgramDefs (ProgDefs defs) = Node "Value definitions" (map toTreeProgDef defs)
toTreeHIRProgramDefs (ProgDataDefs defs) = Node "Data definitions" (map toTreeHIRDataDef defs)
