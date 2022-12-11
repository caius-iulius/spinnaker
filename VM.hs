module VM where
import System.IO(hFlush,stdout,isEOF)
import System.Exit(exitSuccess)
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
    | ICase Int [([VMPat], VMCode)]

instance Show VMInstr where
    show (IConst lit) = show lit
    show (IAccess i) = '$':show i
    show (IClos c) = '\\':show c
    show IApp = "APP"
    show IRet = "RET"
    show (IVariant n i) = "VAR"++show n++ '(':show i++")"
    show (ICombApp n i) = "COMB"++show n++ '(':show i++")"
    show (ICase i pscs) = "CASE("++show i++")"++show pscs

data VMPatData
    = PConst Literal
    | PVariant Name [VMPat]
    | PWildcard
    deriving Show
type VMPat = (Bool, VMPatData)

data VMVal
    = VConst Literal
    | VVariant Name [VMVal]
    | VClos VMCode VMEnv
    deriving Show

type VMStack = [VMVal]
type VMState = (VMCode, VMStack, VMEnv)
type VMMonad = ReaderT [(Name, VMCode)] IO

execComb :: Name -> VMStack -> VMEnv -> VMMonad VMVal
execComb "_addInt" s (VConst(LitInteger i1):VConst(LitInteger i0):[]) =
    let v = VConst (LitInteger (i0+i1))
    in execVM ([IRet], v:s, [])
execComb "_subInt" s (VConst(LitInteger i1):VConst(LitInteger i0):[]) =
    let v = VConst (LitInteger (i0-i1))
    in execVM ([IRet], v:s, [])
execComb "_mulInt" s (VConst(LitInteger i1):VConst(LitInteger i0):[]) =
    let v = VConst (LitInteger (i0*i1))
    in execVM ([IRet], v:s, [])
execComb "_divInt" s (VConst(LitInteger i1):VConst(LitInteger i0):[]) =
    let v = VConst (LitInteger (div i0 i1))
    in execVM ([IRet], v:s, [])
execComb "_equInt" s (VConst(LitInteger i1):VConst(LitInteger i0):[]) =
    let v = VVariant (if i0 == i1 then "True#BI" else "False#BI") []
    in execVM ([IRet], v:s, [])
execComb "_neqInt" s (VConst(LitInteger i1):VConst(LitInteger i0):[]) =
    let v = VVariant (if i0 /= i1 then "True#BI" else "False#BI") []
    in execVM ([IRet], v:s, [])
execComb "_leqInt" s (VConst(LitInteger i1):VConst(LitInteger i0):[]) =
    let v = VVariant (if i0 <= i1 then "True#BI" else "False#BI") []
    in execVM ([IRet], v:s, [])
execComb "_greInt" s (VConst(LitInteger i1):VConst(LitInteger i0):[]) =
    let v = VVariant (if i0 > i1 then "True#BI" else "False#BI") []
    in execVM ([IRet], v:s, [])

execComb "_addFlt" s (VConst(LitFloating f1):VConst(LitFloating f0):[]) =
    let v = VConst (LitFloating (f0+f1))
    in execVM ([IRet], v:s, [])
execComb "_subFlt" s (VConst(LitFloating f1):VConst(LitFloating f0):[]) =
    let v = VConst (LitFloating (f0-f1))
    in execVM ([IRet], v:s, [])
execComb "_mulFlt" s (VConst(LitFloating f1):VConst(LitFloating f0):[]) =
    let v = VConst (LitFloating (f0*f1))
    in execVM ([IRet], v:s, [])
execComb "_divFlt" s (VConst(LitFloating f1):VConst(LitFloating f0):[]) =
    let v = VConst (LitFloating (f0/f1))
    in execVM ([IRet], v:s, [])
execComb "_equFlt" s (VConst(LitFloating f1):VConst(LitFloating f0):[]) =
    let v = VVariant (if f0 == f1 then "True#BI" else "False#BI") []
    in execVM ([IRet], v:s, [])
execComb "_neqFlt" s (VConst(LitFloating f1):VConst(LitFloating f0):[]) =
    let v = VVariant (if f0 /= f1 then "True#BI" else "False#BI") []
    in execVM ([IRet], v:s, [])
execComb "_leqFlt" s (VConst(LitFloating f1):VConst(LitFloating f0):[]) =
    let v = VVariant (if f0 <= f1 then "True#BI" else "False#BI") []
    in execVM ([IRet], v:s, [])
execComb "_greFlt" s (VConst(LitFloating f1):VConst(LitFloating f0):[]) =
    let v = VVariant (if f0 > f1 then "True#BI" else "False#BI") []
    in execVM ([IRet], v:s, [])
execComb "_convItoF" s (VConst(LitInteger i):[]) =
    execVM ([IRet], (VConst(LitFloating(fromIntegral i))):s, [])
execComb "_floorFlt" s (VConst(LitFloating f):[]) =
    execVM ([IRet], (VConst(LitInteger(floor f))):s, [])

execComb "_convItoC" s (VConst(LitInteger i):[]) =
    execVM ([IRet], (VConst(LitCharacter(chr i))):s, [])
execComb "_convCtoI" s (VConst(LitCharacter c):[]) =
    execVM ([IRet], (VConst(LitInteger(ord c))):s, [])
execComb "_putChr" s (rw:VConst(LitCharacter ch):[]) = do
    lift $ putChar ch
    execVM ([IRet], rw:s, [])
execComb "_getChr" s (rw:[]) = do
    lift $ hFlush stdout
    c <- lift getChar
    execVM ([IRet], (VVariant "(,)" [VConst(LitCharacter c), rw]):s, [])
execComb "_isEOF" s (rw:[]) = do
    cond <- lift isEOF
    let v = VVariant (if cond then "True#BI" else "False#BI") []
    execVM ([IRet], (VVariant "(,)" [v, rw]):s, [])

execComb "_exit" s (rw:[]) = lift $ exitSuccess

execComb n s e = do
    g <- ask
    let c = case lookup n g of
                Just c -> c
                Nothing -> error $ "LOOKUP:" ++ show n
    execVM (c,s,e)

sievePatternInner v PWildcard = return []
sievePatternInner (VConst vlit) (PConst plit)
    | vlit == plit = return []
    | otherwise = Nothing
sievePatternInner (VVariant vn vas) (PVariant pn pas)
    | vn == pn = sievePatterns vas pas
    | otherwise = Nothing
sievePatternInner v p = error $ "UNMATCHED PAT:" ++ show v ++ show p
sievePattern v (True, p) = fmap (v :) (sievePatternInner v p)
sievePattern v (False, p) = sievePatternInner v p
sievePatterns :: [VMVal] -> [VMPat] -> Maybe [VMVal]
sievePatterns vs ps = fmap concat $ zipWithM sievePattern vs ps

chooseBranch vs ((ps,c):pscs) =
    case sievePatterns vs ps of
        Nothing -> chooseBranch vs pscs
        Just bs -> (bs, c)
chooseBranch vs [] = error $ "Pattern match failed on values (non-exhaustive): " ++ show vs

execVM :: VMState -> VMMonad VMVal
execVM (IRet:c, v:[], e) = return v
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
execVM (ICase i pscs:IRet:_, s, e) = --TCO case
    let (vs,s') = splitAt i s
        (bs, c') = chooseBranch (reverse vs) pscs
    in execVM (c', s', reverse bs ++ e)
execVM (ICase i pscs:c, s, e) =
    let (vs,s') = splitAt i s
        (bs, c') = chooseBranch (reverse vs) pscs
    in execVM (c', VClos c e:s', reverse bs ++ e)
execVM (c, s, e) = error $ "INVALID STATE:" ++ show c ++ show s ++ show e

evalProg :: (VMCode, [(String, VMCode)]) -> IO ()
evalProg (ep, defs) = fmap (const ()) $ runReaderT (execVM (ep, [], [])) defs
