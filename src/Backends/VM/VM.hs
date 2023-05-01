module Backends.VM.VM where

import System.IO(hFlush,stdout,isEOF)
import System.Exit(exitWith, ExitCode(..))
import Control.Monad.Reader
import Data.Char(ord,chr)

import HLDefs(Literal(..))

type VMCode = [VMInstr]
type VMEnv = [VMVal]
type Name = String

data VMInstr
    = IConst Literal
    | IAccess Int
    | IClos VMCode
    | IApp
    | IRet
    | IVariant Name Int
    | ICombApp Name Int
    | ITest VMPat VMCode VMCode
    | ILet
    | IUnlet
    | IError String

instance Show VMInstr where
    show (IConst lit) = show lit
    show (IAccess i) = '$':show i
    show (IClos c) = '\\':show c
    show IApp = "APP"
    show IRet = "RET"
    show (IVariant n i) = "VAR"++show n++ '(':show i++")"
    show (ICombApp n i) = "COMB"++show n++ '(':show i++")"
    show (ITest pat c0 c1) = "CASE("++show pat++")"++ "POS("++show c0 ++")NEG("++ show c1++")"
    show ILet = "LET"
    show IUnlet = "UNLET"
    show (IError s) = "ERROR(" ++ show s ++ ")"

data VMPat
    = PConst Literal
    | PVariant Name
    deriving Show

data VMVal
    = VConst Literal
    | VVariant Name [VMVal]
    | VClos VMCode VMEnv
    deriving Show

type VMStack = [VMVal]
type VMState = (VMCode, VMStack, VMEnv)
type VMMonad = ReaderT [(Name, VMCode)] IO

execComb :: Name -> VMStack -> VMEnv -> VMMonad VMVal
execComb "spinnaker_addInt" s [VConst(LitInteger i1),VConst(LitInteger i0)] =
    let v = VConst (LitInteger (i0+i1))
    in execVM ([IRet], v:s, [])
execComb "spinnaker_subInt" s [VConst(LitInteger i1),VConst(LitInteger i0)] =
    let v = VConst (LitInteger (i0-i1))
    in execVM ([IRet], v:s, [])
execComb "spinnaker_mulInt" s [VConst(LitInteger i1),VConst(LitInteger i0)] =
    let v = VConst (LitInteger (i0*i1))
    in execVM ([IRet], v:s, [])
execComb "spinnaker_divInt" s [VConst(LitInteger i1),VConst(LitInteger i0)] =
    let v = VConst (LitInteger (quot i0 i1))
    in execVM ([IRet], v:s, [])
execComb "spinnaker_remInt" s [VConst(LitInteger i1),VConst(LitInteger i0)] =
    let v = VConst (LitInteger (rem i0 i1))
    in execVM ([IRet], v:s, [])
execComb "spinnaker_equInt" s [VConst(LitInteger i1),VConst(LitInteger i0)] =
    let v = VVariant (if i0 == i1 then "True" else "False") []
    in execVM ([IRet], v:s, [])
execComb "spinnaker_neqInt" s [VConst(LitInteger i1),VConst(LitInteger i0)] =
    let v = VVariant (if i0 /= i1 then "True" else "False") []
    in execVM ([IRet], v:s, [])
execComb "spinnaker_leqInt" s [VConst(LitInteger i1),VConst(LitInteger i0)] =
    let v = VVariant (if i0 <= i1 then "True" else "False") []
    in execVM ([IRet], v:s, [])
execComb "spinnaker_greInt" s [VConst(LitInteger i1),VConst(LitInteger i0)] =
    let v = VVariant (if i0 > i1 then "True" else "False") []
    in execVM ([IRet], v:s, [])

execComb "spinnaker_addFlt" s [VConst(LitFloating f1),VConst(LitFloating f0)] =
    let v = VConst (LitFloating (f0+f1))
    in execVM ([IRet], v:s, [])
execComb "spinnaker_subFlt" s [VConst(LitFloating f1),VConst(LitFloating f0)] =
    let v = VConst (LitFloating (f0-f1))
    in execVM ([IRet], v:s, [])
execComb "spinnaker_mulFlt" s [VConst(LitFloating f1),VConst(LitFloating f0)] =
    let v = VConst (LitFloating (f0*f1))
    in execVM ([IRet], v:s, [])
execComb "spinnaker_divFlt" s [VConst(LitFloating f1),VConst(LitFloating f0)] =
    let v = VConst (LitFloating (f0/f1))
    in execVM ([IRet], v:s, [])
execComb "spinnaker_equFlt" s [VConst(LitFloating f1),VConst(LitFloating f0)] =
    let v = VVariant (if f0 == f1 then "True" else "False") []
    in execVM ([IRet], v:s, [])
execComb "spinnaker_neqFlt" s [VConst(LitFloating f1),VConst(LitFloating f0)] =
    let v = VVariant (if f0 /= f1 then "True" else "False") []
    in execVM ([IRet], v:s, [])
execComb "spinnaker_leqFlt" s [VConst(LitFloating f1),VConst(LitFloating f0)] =
    let v = VVariant (if f0 <= f1 then "True" else "False") []
    in execVM ([IRet], v:s, [])
execComb "spinnaker_greFlt" s [VConst(LitFloating f1),VConst(LitFloating f0)] =
    let v = VVariant (if f0 > f1 then "True" else "False") []
    in execVM ([IRet], v:s, [])
execComb "spinnaker_convItoF" s [VConst(LitInteger i)] =
    execVM ([IRet], VConst(LitFloating(fromIntegral i)):s, [])
execComb "spinnaker_floorFlt" s [VConst(LitFloating f)] =
    execVM ([IRet], VConst(LitInteger(floor f)):s, [])

execComb "spinnaker_andBool" s [VVariant b1 [],VVariant b0 []] =
    let b = case (b0, b1) of
            ("True", "True") -> "True"
            ("True", "False") -> "False"
            ("False", "True") -> "False"
            ("False", "False") -> "False"
    in execVM ([IRet], VVariant b []:s, [])
execComb "spinnaker_orBool" s [VVariant b1 [],VVariant b0 []] =
    let b = case (b0, b1) of
            ("True", "True") -> "True"
            ("True", "False") -> "True"
            ("False", "True") -> "True"
            ("False", "False") -> "False"
    in execVM ([IRet], VVariant b []:s, [])
execComb "spinnaker_notBool" s [VVariant b0 []] =
    let b = case b0 of
            "True" -> "False"
            "False" -> "True"
    in execVM ([IRet], VVariant b []:s, [])
execComb "spinnaker_convItoC" s [VConst(LitInteger i)] =
    execVM ([IRet], VConst(LitCharacter(chr i)):s, [])
execComb "spinnaker_convCtoI" s [VConst(LitCharacter c)] =
    execVM ([IRet], VConst(LitInteger(ord c)):s, [])
execComb "spinnaker_putChr" s [rw,VConst(LitCharacter ch)] = do
    lift $ putChar ch
    execVM ([IRet], rw:s, [])
execComb "spinnaker_getChr" s [rw] = do
    lift $ hFlush stdout
    c <- lift getChar
    execVM ([IRet], VVariant "(,)" [VConst(LitCharacter c), rw]:s, [])
execComb "spinnaker_isEOF" s [rw] = do
    cond <- lift isEOF
    let v = VVariant (if cond then "True" else "False") []
    execVM ([IRet], VVariant "(,)" [v, rw]:s, [])

execComb "spinnaker_exit" s [rw, VConst(LitInteger i)] = lift (exitWith (if i == 0 then ExitSuccess else ExitFailure i))

execComb n s e = do
    g <- ask
    let c = case lookup n g of
                Just myc -> myc
                Nothing -> error $ "LOOKUP:" ++ show n ++ show e
    execVM (c,s,e)

chooseBranch :: VMVal -> VMPat -> [VMInstr] -> [VMInstr] -> ([VMVal], [VMInstr])
chooseBranch (VConst vlit) (PConst plit) c0 c1
    | vlit == plit = ([], c0)
    | otherwise = ([], c1)
chooseBranch (VVariant vc args) (PVariant pc) c0 c1
    | vc == pc = (args, c0)
    | otherwise = ([], c1)

execVM :: VMState -> VMMonad VMVal
execVM (IRet:c, [v], e) = return v
execVM (IConst k:c, s, e) = execVM (c, VConst k:s, e)
execVM (IAccess i:c, s, e) = execVM (c, (e!!i):s, e)
execVM (IClos c':c, s, e) = execVM (c, VClos c' e:s, e)
execVM (IApp:IRet:_, a:VClos c' e':s, e) = execVM (c', s, a:e') --TCO clos
execVM (IApp:c, a:VClos c' e':s, e) = execVM (c', VClos c e:s, a:e')
execVM (IRet:c, r:VClos c' e':s, e) = execVM (c', r:s, e')
execVM (IVariant n i:c, s, e) =
    let (as,s') = splitAt i s
    in execVM (c, VVariant n (reverse as):s', e)
execVM (ICombApp n i:IRet:_, s, e) = --TCO comb
    let (as,s') = splitAt i s
    in execComb n s' as
execVM (ICombApp n i:c, s, e) = 
    let (as,s') = splitAt i s
    in execComb n (VClos c e:s') as
execVM (ITest pat c0 c1:IRet:_, v:s, e) = --TCO case
    let (bs, c') = chooseBranch v pat c0 c1
    in execVM (c', s, reverse bs ++ e)
execVM (ITest pat c0 c1:c, v:s, e) =
    let (bs, c') = chooseBranch v pat c0 c1
    in execVM (c', VClos c e:s, reverse bs ++ e)
execVM (ILet:c, v:s, e) = execVM (c, s, v:e)
execVM (IUnlet:c, s, _:e) = execVM (c, s, e)
execVM (IError s:_, _, _) = error s
execVM (c, s, e) = error $ "INVALID STATE:" ++ show c ++ show s ++ show e

evalProg :: (VMCode, [(String, VMCode)]) -> IO ()
evalProg (ep, defs) = const () <$> runReaderT (execVM (ep, [], [])) defs
