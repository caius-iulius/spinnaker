module Typer (typeProgram) where
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
builtinDemodTypes = ["->", "Int", "Flt", "Bool"]--, "List"]
builtinDemodVals = ["_addInt", "_subInt", "_mulInt", "_divInt", "_equInt", "_neqInt", "_leqInt", "_greInt", "_putChr", "_getChr"]
builtinDemodVars = ["True", "False"]--, "Nil", "Cons"]

buildBIDemod l = (l, (Public, l++"#BI"))
buildBIDemodMap = Map.fromList . map buildBIDemod

initCoreDemodEnv = DemodEnv Map.empty (buildBIDemodMap builtinDemodVals) (buildBIDemodMap builtinDemodTypes) (buildBIDemodMap builtinDemodVars)

--Definizioni builtin per Typing
builtinTypingTypes =
    [   ("->#BI", KFun KStar (KFun KStar KStar))
    ,   ("Int#BI", KStar)
    ,   ("Flt#BI", KStar)
    ,   ("Bool#BI", KStar)
    --TEMPORANEI
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
    --TEMPORANEI
    --,   VariantData "Nil#BI" [TyQuant 0 KStar] [] (listT (DataQuant (TyQuant 0 KStar)))
    --,   VariantData "Cons#BI" [TyQuant 0 KStar] [listT (DataQuant (TyQuant 0 KStar)), DataQuant (TyQuant 0 KStar)] (listT (DataQuant (TyQuant 0 KStar)))
    ]
initTypingEnv = (TypingEnv (Map.fromList builtinTypingVals) (Map.fromList builtinTypingTypes) (Map.fromList $ map (\v@(VariantData l _ _ _)->(l,v)) builtinTypingVars))

--Programma typer

typeBlockProgram (BlockProgram ddefgroups vdefgroups) = do
    (ks, e, ddefgroups') <- typeDataDefGroups initTypingEnv ddefgroups
    (ts, e', vdefgroups') <- typeValDefGroups e vdefgroups
    lift $ lift $ putStrLn $ "Final type substitution: " ++ show ts
    lift $ lift $ putStrLn $ "Final kind substitution: " ++ show ks
    lift $ lift $ putStrLn $ "Final env: " ++ show e'
    lift $ lift $ putStrLn $ "Final env freetyvars: " ++ show (freetyvars e')
    return (BlockProgram ddefgroups' vdefgroups')

typeProgram :: SyntaxModule -> SyntaxModule -> IO (Either String (String, BlockProgram))
typeProgram core program = do
    eitherBlock <- demodProgram initCoreDemodEnv core program
    case eitherBlock of
        Left e -> return $ Left e
        Right (kq, tq, ((DemodEnv _ vs _ _), block)) -> case Map.lookup "main" vs of
            Nothing -> return $ Left "Entry point \"main\" is not defined"
            Just (_, entryPoint) -> do
                res <- (runTyperState (TIState kq tq) $ typeBlockProgram block)
                return $ fst res >>= (return . ((,) entryPoint))
