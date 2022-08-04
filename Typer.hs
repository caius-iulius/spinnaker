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
builtinDemodTypes = ["->", "Int", "Flt", "Bool", "Chr", "RealWorld_"]
builtinDemodVars = ["True", "False", "RealWorld_"]

buildBIDemod l = (l, (Public, l++"#BI"))
buildBIDemodMap = Map.fromList . map buildBIDemod

initCoreDemodEnv = DemodEnv Map.empty Map.empty (buildBIDemodMap builtinDemodTypes) (buildBIDemodMap builtinDemodVars) Map.empty

--Definizioni builtin per Typing
builtinTypingTypes =
    [   ("->#BI", KFun KType (KFun KType KType))
    ,   ("Int#BI", KType)
    ,   ("Flt#BI", KType)
    ,   ("Bool#BI", KType)
    ,   ("Chr#BI", KType)
    ,   ("RealWorld_#BI", KType)
    ]
builtinTypingVars =
    [   VariantData "True#BI" [] [] boolT
    ,   VariantData "False#BI" [] [] boolT
    ,   VariantData "RealWorld_#BI" [] [] realworldT
    ]
initTypingEnv = TypingEnv Map.empty (Map.fromList builtinTypingTypes) (Map.fromList $ map (\v@(VariantData l _ _ _)->(l,v)) builtinTypingVars) Map.empty Map.empty

--Programma typer
typeBlockProgram (BlockProgram ddefgroups reldefs extdefs vdefgroups instdefs) = do
    (ks, e, ddefgroups') <- typeDataDefGroups initTypingEnv ddefgroups
    extdefs' <- typeExtDefs e extdefs
    let e' = extDefsInEnv e extdefs'
    vdefgroups' <- completeVariantValDefGroups e' vdefgroups
    instdefs' <- completeVariantInstDefs e' instdefs
    (ks', e'', reldefs') <- typeRelDefs e' reldefs
    (ks'', e''', instdefs'') <- typeKInstDefs (addRelDecls e'') instdefs'
    vdefgroups'' <- typeValDefHints e'' vdefgroups'
    (ts, e'''', vdefgroups''') <- typeValDefGroups e''' vdefgroups''
    instdefs''' <- typeInstDefs e'''' instdefs''
    lift $ lift $ putStrLn $ "Final kind substitution (datas): " ++ show ks
    lift $ lift $ putStrLn $ "Final kind substitution (rels): " ++ show ks'
    lift $ lift $ putStrLn $ "Final kind substitution (insts): " ++ show ks''
    lift $ lift $ putStrLn $ "Final type substitution: " ++ show ts
    lift $ lift $ putStrLn $ "Final env: " ++ show e''''
    lift $ lift $ putStrLn $ "Final env freetyvars: " ++ show (freetyvars e'''')
    return (e'''', BlockProgram ddefgroups' reldefs' extdefs' vdefgroups''' instdefs''')


entryPointBlock env = do
    hle <- demodExpr env syne
    let entryPointVDef = ValDef c "entryPoint#BI" (Just (Qual [] realworldT)) [] hle
    return $ BlockProgram [] [] [] [[entryPointVDef]] []
    where c = Coord "entryPoint" 0 0
          syne = (c, SynExprApp (c, SynExprLabel (Path ["Core", "UnsafeIO"] "runTopIO"))
                    (c, SynExprApp (c, SynExprLabel (Path ["Core"] "runProgramTop")) (c, SynExprLabel (Path [] "main"))))

typeProgram :: String -> TyperState (TypingEnv, HLExpr, BlockProgram)
typeProgram fname = do
    lift $ lift $ putStrLn $ "Init typing env: " ++ show initTypingEnv
    (denv, block) <- demodProgram initCoreDemodEnv "stdlib/core" "stdlib/std" fname
    entry <- entryPointBlock denv
    let block' = concatBlockPrograms block entry
    lift $ lift $ putStrLn $ "DemodProgram:\n" ++ (drawTree $ toTreeBlockProgram block')
    (env, tyblock) <- typeBlockProgram block'
    lift $ lift $ putStrLn $ "Typed Program:\n" ++ (drawTree $ toTreeBlockProgram tyblock)
    return (env, (Coord "entryPoint" 0 0, realworldT, ExprLabel "entryPoint#BI"), tyblock)
