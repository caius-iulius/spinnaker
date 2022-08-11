module Typer (typeBlockProgram) where
import qualified Data.Map as Map
import Control.Monad.Trans

import HLDefs
import TypingDefs
import KindTyper
import TypeTyper
import VariantComplete

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
    typerLog $ "Final kind substitution (datas): " ++ show ks
    typerLog $ "Final kind substitution (rels): " ++ show ks'
    typerLog $ "Final kind substitution (insts): " ++ show ks''
    typerLog $ "Final type substitution: " ++ show ts
    typerLog $ "Final env: " ++ show e''''
    typerLog $ "Final env freetyvars: " ++ show (freetyvars e'''')
    return (e'''', BlockProgram ddefgroups' reldefs' extdefs' vdefgroups''' instdefs''')
