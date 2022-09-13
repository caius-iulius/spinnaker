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
toTreeHLExpr (c, dt, ExprCombinator l es) = Node (show c ++ " DT:" ++ show dt ++ " Combinator: " ++ show l) (map toTreeHLExpr es)
toTreeHLExpr (c, dt, ExprLambda p expr) = Node (show c ++ " DT:" ++ show dt ++ " Lambda") [Node "arg" [toTreeHLPattern p], Node "expr" [toTreeHLExpr expr]]
toTreeHLExpr (c, dt, ExprPut vals branches) = Node (show c ++ " DT:" ++ show dt ++ " Put") [Node "vals" (map toTreeHLExpr vals), Node "branches" (map (\(p, e) -> Node "branch" [Node "pat" [toTreeHLPattern p], Node "expr" [toTreeHLExpr e]]) branches)]
toTreeHLExpr (c, dt, ExprHint hint e) = Node (show c ++ " DT:" ++ show dt ++ " Hinting with type: " ++ show hint) [toTreeHLExpr e]

toTreeHLValDef (ValDef c s t ps e) = Node (show c ++ " Defining val: " ++ show s ++ " typehint: " ++ show t ++ " qualifiers: " ++ show ps) [toTreeHLExpr e]

toTreeHLExtDef (ExtDef c l tas tr) = Node (show c ++ " External combinator: " ++ show l) [Node "with arg " $ map (\ta->Node (show ta)[]) tas, Node "and return type" [Node (show tr) []]]
toTreeHLDataVariant (DataVariant c labl args) = Node (show c ++ " DataVariant: " ++ show labl) (map (\t->Node ("Arg: " ++ show t) []) args)
toTreeHLDataDef (DataDef c labl quants variants) = Node (show c ++ " Defining data: " ++ show labl ++ " with quantifiers: " ++ show quants)
    (map toTreeHLDataVariant variants)

toTreeHLRelDef (RelDef c label quants preds decls) = Node (show c ++ " Defining rel: " ++ show preds ++ " => " ++ show label ++ show quants ++ " declares: ") (map (\(c, l, t)->Node (show c ++ " Decl: " ++ l ++ " of type: " ++ show t) []) decls)
toTreeHLInstDef (InstDef c qualpred defs) = Node (show c ++ " Defining inst: " ++ show qualpred) (map (\(c, l, e)->Node (show c ++ " Def: " ++ show l) [toTreeHLExpr e]) defs)

toTreeBlockProgram (BlockProgram datagroups reldefs extdefs valgroups instdefs) = Node "BlockProgram" [
        Node "Datas" (map (\group->Node "Group of datas" (map toTreeHLDataDef group)) datagroups),
        Node "Rels" (map toTreeHLRelDef reldefs),
        Node "Exts" (map toTreeHLExtDef extdefs),
        Node "Vals" (map (\group->Node "Group of vals" (map toTreeHLValDef group)) valgroups),
        Node "Insts" (map toTreeHLInstDef instdefs)
    ]

toTreeMonoDef (l, e) = Node (show l) [toTreeHLExpr e]
toTreeMonoDefs defs = Node "MonoDefs" (map toTreeMonoDef defs)
--Roba per Syn
toTreeSynPattern p = Node (show p) []

toTreeSynExpr (c, SynExprLiteral l) = Node (show c ++ " Literal: " ++ show l) []
toTreeSynExpr (c, SynExprApp f a) = Node (show c ++ " Function call") [toTreeSynExpr f, toTreeSynExpr a]
toTreeSynExpr (c, SynExprLabel l) = Node (show c ++ " Label: " ++ show l) []
toTreeSynExpr (c, SynExprConstructor l) = Node (show c ++ " Constructor: " ++ show l) []
toTreeSynExpr (c, SynExprTuple es) = Node (show c ++ " Tuple") (map toTreeSynExpr es)
toTreeSynExpr (c, SynExprLambda p expr) = Node (show c ++ " Lambda") [Node "arg" [toTreeSynPattern p], Node "expr" [toTreeSynExpr expr]]
toTreeSynExpr (c, SynExprSndSection op expr) = Node (show c ++ " Second section of operator: " ++ show op) [toTreeSynExpr expr]
toTreeSynExpr (c, SynExprPut vals branches) = Node (show c ++ " Put") [Node "vals" (map toTreeSynExpr vals), Node "branches" (map (\(p, e) -> Node "branch" [Node "pat" [toTreeSynPattern p], Node "expr" [toTreeSynExpr e]]) branches)]
toTreeSynExpr (c, SynExprString s) = Node (show c ++ "String literal: " ++ show s) []
toTreeSynExpr (c, SynExprListNil) = Node (show c ++ " Empty List") []
toTreeSynExpr (c, SynExprListConss es final) = Node (show c ++ " List") (map toTreeSynExpr es ++ [Node "With final elems" [toTreeSynExpr final]])
toTreeSynExpr (c, SynExprIfThenElse cond iftrue iffalse) = Node (show c ++ " IfThenElse") [Node "Condition" [toTreeSynExpr cond], Node "If True" [toTreeSynExpr iftrue], Node "If False" [toTreeSynExpr iffalse]]
toTreeSynExpr (c, SynExprInlineUse path e) = Node (show c ++ "Inline use: " ++ show path) [toTreeSynExpr e]
toTreeSynExpr (c, SynExprBind pat me fe) = Node (show c ++ "Monadic bind to pattern: " ++ show pat) [toTreeSynExpr me, toTreeSynExpr fe]
toTreeSynExpr (c, SynExprHint hint e) = Node (show c ++ "Hinting with type") [toTreeSynTypeExpr hint, toTreeSynExpr e]

toTreeSynValDef (SynValDef c v s te e) = Node (show c ++ " Defining " ++ show v ++ " val: " ++ show s ++ " typehint: " ++ show te) [toTreeSynExpr e]

toTreeSynTypeExpr :: SyntaxTypeExpr -> Tree String
toTreeSynTypeExpr te = Node (show te) []

toTreeSynDataVariant (SynDataVariant c labl args) = Node (show c ++ " DataVariant: " ++ show labl) (map toTreeSynTypeExpr args)

toTreeSynDataDef (SynDataDef c v labl quants variants) = Node (show c ++ " Defining " ++ show v ++ " data: " ++ show labl ++ " with quantifiers: " ++ show quants)
    (map toTreeSynDataVariant variants)

toTreeSynRelValDecl (c, l, te) = Node (show c ++ " Declare val: " ++ show l ++ " of type: " ++ show te) []
toTreeSynModDef (ModMod c v l m) = Node (show c ++ " Defining " ++ show v ++ " module: " ++ show l) [toTreeSynMod m]
toTreeSynModDef (ModFromFile c v l f) = Node (show c ++ " Importing " ++ show v ++ " module: " ++ show l ++ " from file " ++ show f) []
toTreeSynModDef (ModUse c v p) = Node (show c ++ " Using " ++ show v ++ " module: " ++ show p) []
toTreeSynModDef (ModTypeSyn c v l qs e) = Node (show c ++ " " ++ show v ++ " type synonym: " ++ show l ++ " tyargs: " ++ show qs) [toTreeSynTypeExpr e]
toTreeSynModDef (ModValGroup vvdefs) = Node "Group of vals" (map toTreeSynValDef vvdefs)
toTreeSynModDef (ModDataGroup group) = Node "Group of datas" (map toTreeSynDataDef group)
toTreeSynModDef (ModRel c v preds l qs defs) = Node (show c ++ " " ++ show v ++ " rel definition: " ++ show l ++ " tyargs: " ++ show qs ++ " with preds: {" ++ show preds ++ "}") (map toTreeSynRelValDecl defs)
toTreeSynModDef (ModInst c qs preds head instdefs) = Node (show c ++ " Instance definition of: " ++ show head ++ " quantified with forall." ++ show qs ++ "{" ++ show preds ++ "}" ++ " with inst_val_defs") (map (\(c', l, e)->Node ("Defining: " ++ show l) [toTreeSynExpr e]) instdefs)
toTreeSynModDef (ModExt c v l tas tr) = Node (show c ++ " Declaring " ++ show v ++ " combinator") [Node "with argument type" (map toTreeSynTypeExpr tas), Node "and return type" [toTreeSynTypeExpr tr]]
toTreeSynMod (Module defs) = Node "Module" (map toTreeSynModDef defs)
