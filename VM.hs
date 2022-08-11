module VM where
import Control.Monad.Reader
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
    | ICase [(VMPat, VMCode)]
    deriving Show

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
execComb "_putChr" s (rw:VConst(LitCharacter ch):[]) = do
    lift $ putChar ch
    execVM ([IRet], rw:s, [])
execComb n s e = do
    g <- ask
    let Just c = lookup n g
    execVM (c,s,e)

sievePatternInner v PWildcard = return []
sievePatternInner (VConst vlit) (PConst plit)
    | vlit == plit = return []
    | otherwise = Nothing
sievePatternInner (VVariant vn vas) (PVariant pn pas)
    | vn == pn =
        fmap concat $ zipWithM sievePattern vas pas
    | otherwise = Nothing
sievePatternInner v p = error $ show v ++ show p
sievePattern :: VMVal -> VMPat -> Maybe [VMVal]
sievePattern v (True, p) = fmap (v :) (sievePatternInner v p)
sievePattern v (False, p) = sievePatternInner v p

choosePattern v ((p,c):pscs) =
    case sievePattern v p of
        Nothing -> choosePattern v pscs
        Just bs -> (bs, c)

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
execVM (ICase pscs:IRet:_, v:s, e) = --TCO case
    let (bs, c') = choosePattern v pscs
    in execVM (c', s, reverse bs ++ e)
execVM (ICase pscs:c, v:s, e) =
    let (bs, c') = choosePattern v pscs
    in execVM (c', VClos c e:s, reverse bs ++ e)
execVM (c, s, e) = error $ show c ++ show s ++ show e

{- globs = [("_putStr", [
        IAccess 1,
        ICase [ ((False, PVariant "Nil" []), [IAccess 0, IRet])
              , ((False, PVariant "Cons" [(True, PWildcard), (True, PWildcard)]), [IAccess 0, IAccess 1, IAccess 2, ICombApp "_putChr" 2, ICombApp "_putStr" 2, IRet])
              ],
        IRet
    ])]
testcode = [
        IConst(LitCharacter 'C'),
        IConst(LitCharacter 'i'),
        IConst(LitCharacter 'a'),
        IConst(LitCharacter 'o'),
        IConst(LitCharacter ' '),
        IConst(LitCharacter 'M'),
        IConst(LitCharacter 'o'),
        IConst(LitCharacter 'n'),
        IConst(LitCharacter 'd'),
        IConst(LitCharacter 'o'),
        IConst(LitCharacter '!'),
        IConst(LitCharacter '\n'),
        IVariant "Nil" 0,
        IVariant "Cons" 2,
        IVariant "Cons" 2,
        IVariant "Cons" 2,
        IVariant "Cons" 2,
        IVariant "Cons" 2,
        IVariant "Cons" 2,
        IVariant "Cons" 2,
        IVariant "Cons" 2,
        IVariant "Cons" 2,
        IVariant "Cons" 2,
        IVariant "Cons" 2,
        IVariant "Cons" 2,
        IVariant "RW" 0,
        ICombApp "_putStr" 2,
        IRet
    ] -}

globs = [("ack",
      [ IAccess 1,
        ICase [ ((False, PConst(LitInteger 0)),
                    [IAccess 0, IConst(LitInteger 1), ICombApp "_addInt" 2, IRet]),
                ((False, PWildcard), [
                        IAccess 0,
                        ICase [
                                ((False, PConst(LitInteger 0)),
                                    [IAccess 1, IConst(LitInteger 1), ICombApp "_subInt" 2, IConst(LitInteger 1), ICombApp "ack" 2, IRet]),
                                ((False, PWildcard),
                                    [IAccess 1, IConst(LitInteger 1), ICombApp "_subInt" 2, IAccess 1, IAccess 0, IConst(LitInteger 1), ICombApp "_subInt" 2, ICombApp "ack" 2, ICombApp "ack" 2, IRet])
                            ],
                        IRet
                    ])],
        IRet
      ])
    ]

testcode = [IConst(LitInteger 3), IConst(LitInteger 9), ICombApp "ack" 2, IRet]

main = runReaderT (execVM (testcode, [], [])) globs >>= print
