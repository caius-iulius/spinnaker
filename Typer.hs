module Typer (typeBlockProgram, typeProgram) where
import qualified Data.Map as Map
import Control.Monad.Trans
import Data.Tree

import MPCL(StdCoord(..))
import PrettyPrinter
import HLDefs
import SyntaxDefs
import Demod
import TypingDefs
import KindTyper
import TypeTyper
import VariantComplete

--Definizioni builtin per Demod
builtinDemodTypes = ["->", "Int", "Flt", "Bool", "Chr"]
builtinDemodVals = ["_addInt", "_subInt", "_mulInt", "_divInt", "_equInt", "_neqInt", "_leqInt", "_greInt",
                    "_putChr", "_getChr",
                    "_convItoC", "_convCtoI"]
builtinDemodVars = ["True", "False"]

buildBIDemod l = (l, (Public, l++"#BI"))
buildBIDemodMap = Map.fromList . map buildBIDemod

initCoreDemodEnv = DemodEnv Map.empty (buildBIDemodMap builtinDemodVals) (buildBIDemodMap builtinDemodTypes) (buildBIDemodMap builtinDemodVars) Map.empty

--Definizioni builtin per Typing
builtinTypingTypes =
    [   ("->#BI", KFun KType (KFun KType KType))
    ,   ("Int#BI", KType)
    ,   ("Flt#BI", KType)
    ,   ("Bool#BI", KType)
    ,   ("Chr#BI", KType)
    ]
builtinTypingVals =
    [   ("_addInt#BI", TyScheme [] (Qual [] $ buildFunType (buildTupType [intT, intT]) intT))
    ,   ("_subInt#BI", TyScheme [] (Qual [] $ buildFunType (buildTupType [intT, intT]) intT))
    ,   ("_mulInt#BI", TyScheme [] (Qual [] $ buildFunType (buildTupType [intT, intT]) intT))
    ,   ("_divInt#BI", TyScheme [] (Qual [] $ buildFunType (buildTupType [intT, intT]) intT))
    ,   ("_equInt#BI", TyScheme [] (Qual [] $ buildFunType (buildTupType [intT, intT]) boolT))
    ,   ("_neqInt#BI", TyScheme [] (Qual [] $ buildFunType (buildTupType [intT, intT]) boolT))
    ,   ("_leqInt#BI", TyScheme [] (Qual [] $ buildFunType (buildTupType [intT, intT]) boolT))
    ,   ("_greInt#BI", TyScheme [] (Qual [] $ buildFunType (buildTupType [intT, intT]) boolT))
    ,   ("_convItoC#BI", TyScheme [] (Qual [] $ buildFunType intT chrT))
    ,   ("_convCtoI#BI", TyScheme [] (Qual [] $ buildFunType chrT intT))
    --TEMPORANEI
    ,   ("_putChr#BI", TyScheme [] (Qual [] $ buildFunType chrT (buildTupType [])))
    ,   ("_getChr#BI", TyScheme [] (Qual [] $ buildFunType (buildTupType []) chrT))
    ]
builtinTypingVars =
    [   VariantData "True#BI" [] [] boolT
    ,   VariantData "False#BI" [] [] boolT
    ]
builtinTypingRels = []
initTypingEnv = TypingEnv (Map.fromList builtinTypingVals) (Map.fromList builtinTypingTypes) (Map.fromList $ map (\v@(VariantData l _ _ _)->(l,v)) builtinTypingVars) (Map.fromList builtinTypingRels)

--Programma typer
typeBlockProgram (BlockProgram ddefgroups reldefs vdefgroups instdefs) = do
    (ks, e, ddefgroups') <- typeDataDefGroups initTypingEnv ddefgroups
    vdefgroups' <- completeVariantValDefGroups e vdefgroups
    instdefs' <- completeVariantInstDefs e instdefs
    (ks', e', reldefs') <- typeRelDefs e reldefs
    (ks'', e'', instdefs'') <- typeKInstDefs (addRelDecls e') instdefs'
    vdefgroups'' <- typeValDefHints e'' vdefgroups'
    (ts, e''', vdefgroups''') <- typeValDefGroups e'' vdefgroups''
    instdefs''' <- typeInstDefs e''' instdefs''
    lift $ lift $ putStrLn $ "Final kind substitution (datas): " ++ show ks
    lift $ lift $ putStrLn $ "Final kind substitution (rels): " ++ show ks'
    lift $ lift $ putStrLn $ "Final kind substitution (insts): " ++ show ks''
    lift $ lift $ putStrLn $ "Final type substitution: " ++ show ts
    lift $ lift $ putStrLn $ "Final env: " ++ show e'''
    lift $ lift $ putStrLn $ "Final env freetyvars: " ++ show (freetyvars e''')
    return (e''', BlockProgram ddefgroups' reldefs' vdefgroups''' instdefs''')


entryPointBlock env = do
    hle <- demodExpr env syne
    let entryPointVDef = ValDef c "entryPoint#BI" (Just (Qual [] (buildTupType []))) [] hle
    return $ BlockProgram [] [] [[entryPointVDef]] []
    where c = Coord "entryPoint" 0 0
          syne = (c, SynExprApp (c, SynExprLabel (Path ["Core"] "putStrLn")) (c, SynExprApp (c, SynExprLabel (Path ["Core"] "show")) (c, SynExprLabel (Path [] "main"))))

typeProgram :: SyntaxModule -> SyntaxModule -> TyperState (TypingEnv, String, BlockProgram)
typeProgram core program = do
    lift $ lift $ putStrLn $ "Init typing env: " ++ show initTypingEnv
    (denv, block) <- demodProgram initCoreDemodEnv core program
    entry <- entryPointBlock denv
    let block' = concatBlockPrograms block entry
    lift $ lift $ putStrLn $ "DemodProgram:\n" ++ (drawTree $ toTreeBlockProgram block')
    (env, tyblock) <- typeBlockProgram block'
    return (env, "entryPoint#BI", tyblock)
