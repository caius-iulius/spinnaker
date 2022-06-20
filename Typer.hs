module Typer (typeBlockProgram, typeProgram) where
import qualified Data.Map as Map
import Control.Monad.Trans
import Data.Tree
import PrettyPrinter
import HLDefs
import SyntaxDefs
import Demod
import TypingDefs
import KindTyper
import TypeTyper

--Definizioni builtin per Demod
builtinDemodTypes = ["->", "Int", "Flt", "Bool"]
builtinDemodVals = ["_addInt", "_subInt", "_mulInt", "_divInt", "_equInt", "_neqInt", "_leqInt", "_greInt", "_putChr", "_getChr"]
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
    ]
builtinTypingVals =
    [   ("_addInt#BI", TyScheme [] (buildFunType (buildTupType [intT, intT]) intT))
    ,   ("_subInt#BI", TyScheme [] (buildFunType (buildTupType [intT, intT]) intT))
    ,   ("_mulInt#BI", TyScheme [] (buildFunType (buildTupType [intT, intT]) intT))
    ,   ("_divInt#BI", TyScheme [] (buildFunType (buildTupType [intT, intT]) intT))
    ,   ("_equInt#BI", TyScheme [] (buildFunType (buildTupType [intT, intT]) boolT))
    ,   ("_neqInt#BI", TyScheme [] (buildFunType (buildTupType [intT, intT]) boolT))
    ,   ("_leqInt#BI", TyScheme [] (buildFunType (buildTupType [intT, intT]) boolT))
    ,   ("_greInt#BI", TyScheme [] (buildFunType (buildTupType [intT, intT]) boolT))
    --TEMPORANEI
    ,   ("_putChr#BI", TyScheme [] (buildFunType intT (buildTupType [])))
    ,   ("_getChr#BI", TyScheme [] (buildFunType (buildTupType []) intT))
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
    (ks', e', reldefs') <- typeRelDefs e reldefs
    (ks'', e'', instdefs') <- typeKInstDefs e' instdefs
    vdefgroups' <- typeValDefHints e'' vdefgroups
    (ts, e''', vdefgroups'') <- typeValDefGroups e'' vdefgroups'
    lift $ lift $ putStrLn $ "Final kind substitution (datas): " ++ show ks
    lift $ lift $ putStrLn $ "Final kind substitution (rels): " ++ show ks'
    lift $ lift $ putStrLn $ "Final kind substitution (insts): " ++ show ks''
    lift $ lift $ putStrLn $ "Final type substitution: " ++ show ts
    lift $ lift $ putStrLn $ "Final env: " ++ show e'''
    lift $ lift $ putStrLn $ "Final env freetyvars: " ++ show (freetyvars e''')
    return (e''', BlockProgram ddefgroups' reldefs' vdefgroups'' instdefs')

typeProgram :: SyntaxModule -> SyntaxModule -> TyperState (TypingEnv, String, BlockProgram)
typeProgram core program = do
    lift $ lift $ putStrLn $ "Init typing env: " ++ show initTypingEnv
    (DemodEnv _ vs _ _ _, block) <- demodProgram initCoreDemodEnv core program
    case Map.lookup "main" vs of
        Nothing -> fail "Entry point \"main\" is not defined"
        Just (_, entryPoint) -> do
            lift $ lift $ putStrLn $ "DemodProgram:\n" ++ (drawTree $ toTreeBlockProgram block)
            (env, tyblock) <- typeBlockProgram block
            return (env, entryPoint, tyblock)
