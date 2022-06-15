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
toTreeHLExpr (c, dt, ExprLambda p expr) = Node (show c ++ " DT:" ++ show dt ++ " Lambda") [Node "arg" [toTreeHLPattern p], Node "expr" [toTreeHLExpr expr]]
toTreeHLExpr (c, dt, ExprPut val branches) = Node (show c ++ " DT:" ++ show dt ++ " Put") [Node "val" [toTreeHLExpr val], Node "branches" (map (\(p, e) -> Node "branch" [Node "pat" [toTreeHLPattern p], Node "expr" [toTreeHLExpr e]]) branches)]

toTreeHLValDef (ValDef c s t e) = Node (show c ++ " Defining val: " ++ show s ++ " typehint: " ++ show t) [toTreeHLExpr e]

toTreeHLDataVariant (DataVariant c labl args) = Node (show c ++ " DataVariant: " ++ show labl) (map (\(e, t)->Node "Arg" [Node (show e) [], Node (show t) []]) args)
toTreeHLDataDef (DataDef c labl quants variants) = Node (show c ++ " Defining data: " ++ show labl ++ " with quantifiers: " ++ show quants)
    (map toTreeHLDataVariant variants)

toTreeBlockProgram (BlockProgram datagroups valgroups) = Node "BlockProgram" [
        Node "Datas" (map (\group->Node "Group of datas" (map toTreeHLDataDef group)) datagroups),
        Node "Vals" (map (\group->Node "Group of vals" (map toTreeHLValDef group)) valgroups)
    ]

--Roba per Syn
toTreeSynPattern p = Node (show p) []

toTreeSynExpr (c, SynExprLiteral l) = Node (show c ++ " Literal: " ++ show l) []
toTreeSynExpr (c, SynExprApp f a) = Node (show c ++ " Function call") [toTreeSynExpr f, toTreeSynExpr a]
toTreeSynExpr (c, SynExprLabel l) = Node (show c ++ " Label: " ++ show l) []
toTreeSynExpr (c, SynExprConstructor l) = Node (show c ++ " Constructor: " ++ show l) []
toTreeSynExpr (c, SynExprTuple es) = Node (show c ++ " Tuple") (map toTreeSynExpr es)
toTreeSynExpr (c, SynExprLambda p expr) = Node (show c ++ " Lambda") [Node "arg" [toTreeSynPattern p], Node "expr" [toTreeSynExpr expr]]
toTreeSynExpr (c, SynExprPut val branches) = Node (show c ++ " Put") [Node "val" [toTreeSynExpr val], Node "branches" (map (\(p, e) -> Node "branch" [Node "pat" [toTreeSynPattern p], Node "expr" [toTreeSynExpr e]]) branches)]
toTreeSynExpr (c, SynExprListNil) = Node (show c ++ " Empty List") []
toTreeSynExpr (c, SynExprListConss es final) = Node (show c ++ " List") (map toTreeSynExpr es ++ [Node "With final elems" [toTreeSynExpr final]])
toTreeSynExpr (c, SynExprIfThenElse cond iftrue iffalse) = Node (show c ++ " IfThenElse") [Node "Condition" [toTreeSynExpr cond], Node "If True" [toTreeSynExpr iftrue], Node "If False" [toTreeSynExpr iffalse]]
toTreeSynExpr (c, SynExprInlineUse path e) = Node (show c ++ "Inline use: " ++ show path) [toTreeSynExpr e]


toTreeSynValDef (SynValDef c v s te e) = Node (show c ++ " Defining " ++ show v ++ " val: " ++ show s ++ " typehint: " ++ show te) [toTreeSynExpr e]

toTreeSynTypeExpr :: SyntaxTypeExpr -> Tree String
toTreeSynTypeExpr te = Node (show te) []

toTreeSynDataVariant (SynDataVariant c labl args) = Node (show c ++ " DataVariant: " ++ show labl) (map toTreeSynTypeExpr args)

toTreeSynDataDef (SynDataDef c v labl quants variants) = Node (show c ++ " Defining " ++ show v ++ " data: " ++ show labl ++ " with quantifiers: " ++ show quants)
    (map toTreeSynDataVariant variants)

toTreeSynRelValDecl (c, l, te) = Node (show c ++ " Declare val: " ++ show l ++ " of type: " ++ show te) []
toTreeSynModDef (ModMod c v l m) = Node (show c ++ " Defining " ++ show v ++ " module: " ++ show l) [toTreeSynMod m]
toTreeSynModDef (ModUse c v p) = Node (show c ++ " Using " ++ show v ++ " module: " ++ show p) []
toTreeSynModDef (ModTypeSyn c v l qs e) = Node (show c ++ " " ++ show v ++ " type synonym: " ++ show l ++ " tyargs: " ++ show qs) [toTreeSynTypeExpr e]
toTreeSynModDef (ModValGroup vvdefs) = Node "Group of vals" (map toTreeSynValDef vvdefs)
toTreeSynModDef (ModDataGroup group) = Node "Group of datas" (map toTreeSynDataDef group)
toTreeSynModDef (ModRel c v constrs l qs defs) = Node (show c ++ " " ++ show v ++ " rel definition with constraints: " ++ show constrs ++ " labl: " ++ show l ++ " tyargs: " ++ show qs) (map toTreeSynRelValDecl defs)
toTreeSynModDef (ModInst c qpred instdefs) = Node (show c ++ " Instance definition of: " ++ show qpred ++ " with inst_val_defs") (map (\(c', l, e)->Node ("Defining: " ++ show l) [toTreeSynExpr e]) instdefs)
toTreeSynMod (Module defs) = Node "Module" (map toTreeSynModDef defs)
