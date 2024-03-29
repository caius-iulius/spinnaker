--Micro Parser Combinator Library -- Just Enough To Be Dangerous!
module Parser.MPCL where

import GHC.Base
import GHC.Unicode

type ErrMessage = String
data ParseResult coord t
    = POk t (coord, String)
    | PFail coord ErrMessage
    | PFatal coord ErrMessage
    deriving Show

data Parser coord a
    = PValue a
    | PParse ((coord, String)->ParseResult coord a)

instance Applicative (Parser coord) where
    pure = PValue
    (<*>) = ap

instance Monad (Parser coord) where
    (PValue a) >>= f = f a
    (PParse pf) >>= f = PParse(\cs ->
        case pf cs of
            POk e cs1 -> parse (f e) cs1
            PFail c m -> PFail c m
            PFatal c m -> PFatal c m
        )

instance Functor (Parser coord) where
    fmap f p =
        (p >>= (pure . f))

-- Funzione primaria di parsing
parse :: Parser c a -> (c, String) -> ParseResult c a
parse (PValue v) cs = POk v cs
parse (PParse f) cs = f cs

-- Scelta con preferenza a sinistra:
-- (p <|| k) = p se p è valido, altrimenti k
-- TODO magari conviene far vedere tutti i messaggi di errore quando falliscono
infixr 5 <||
(<||) :: Parser c a -> Parser c a -> Parser c a
(PValue v) <|| _ = PValue v
(PParse f) <|| p = PParse(\cs ->
    case f cs of
        PFail _ _ -> parse p cs
        resf -> resf
    )

--Restituisce un parser che non consuma l'input
look :: Parser c a -> Parser c a
look p = PParse(\cs ->
    case parse p cs of
        POk el _ -> POk el cs
        resp -> resp
    )

--Restituisce un parser che fallisce catastroficamente se non è soddisfatto
require :: Parser c a -> Parser c a
require p = PParse(\cs ->
    case parse p cs of
        PFail c e -> PFatal c e
        resp -> resp
    )
--Restituisce un parser che converte i fallimenti catastrofici in fallimenti normali
recover :: Parser c a -> Parser c a
recover p = PParse(\cs ->
    case parse p cs of
        PFatal c e -> PFail c e
        resp -> resp
    )

discard :: Parser c a -> Parser c ()
discard = fmap (const ())
{-
--Aggiunge la stringa specificata all'inizio del messaggio di errore
detailError s p = PParse(\cs ->
    let resp = parse p cs in case resp of
        POk _ _ -> resp
        PFail c preve -> PFail c (s++'\n':preve)-- parse (PPFail (fst cs, s++'\n':preve)) cs
        PFatal c preve -> PFatal c (s++'\n':preve)-- parse (PPFail (fst cs, s++'\n':preve)) cs
    )
-}

--Sostituisce il messaggio di errore con la stringa specificata
--TODO: Forse bisogna conservare le coordinate originarie?
--TODO: Forse sovrascrivi anche l'errore fatale
describeError :: String -> Parser c a -> Parser c a
describeError s p = PParse(\cs ->
    case parse p cs of
        PFail c preve -> PFail (fst cs) s
        resp -> resp
    )

--Messaggio di errore in caso di fallimento "soft"
pfail :: String -> Parser c a
pfail e = PParse(\(c, s) -> PFail c e)
--Messaggio di errore fatale
pfatal :: String -> Parser c a
pfatal e = PParse(\(c, s) -> PFatal c e)

--Ha successo se e solo se si è arrivati alla fine del file
reachedEof :: Parser c ()
reachedEof = PParse(\(c, s) ->
    case s of
        [] -> POk () (c, s)
        xs -> PFail c ("EOF not reached, remaining string: " ++ xs)
    )

--Elabora uno o più elementi del parser specificato
munch1 :: Parser c a -> Parser c [a]
munch1 p = do {
    e <- p;
    es <- munch p;
    return (e:es)
}

--Elabora zero o più elementi del parser specificato
munch :: Parser c a -> Parser c [a]
munch p = munch1 p <|| return []

--Elabora uno o più p separati da sep
sepBy1 :: Parser c p -> Parser c sep -> Parser c [p]
sepBy1 p sep = do {
    e <- p;
    es <- munch (sep >> require p); -- se c'è il separatore è necessario l'elemento
    return (e:es)
}

--Elabora zero o più p separati da sep
sepBy :: Parser c p -> Parser c sep -> Parser c [p]
sepBy p sep = sepBy1 p sep <|| return []

--Elabora due o più p separati da sep
sepBy2 :: Parser c p -> Parser c sep -> Parser c [p]
sepBy2 p sep = do {
    e <- p;
    es <- munch1 (sep >> require p);
    return (e:es)
}

--Se e ha successo il parser fallisce, altrimenti fai p
difference :: Show e => Parser c p -> Parser c e -> Parser c p
difference p e = PParse(\cs ->
    case parse e cs of
        POk res (c, _) -> PFail c ("Unexpected parse: " ++ show res)
        _ -> parse p cs
    )

--Se p è ha successo lo restituisce, altrimenti val
option :: a -> Parser c a -> Parser c a
option val p = p <|| return val

--Se p è ha successo restituisce Just p, altrimenti Nothing
optional :: Parser c a -> Parser c (Maybe a)
optional p = fmap Just p <|| return Nothing

--come ReadP.satisfy, ma newc è una funzione da una coordinata alla successiva, questo dà la possibilità di cambiare sistema di riferimento
satisfyInternal :: (c -> Char -> c) -> (Char -> Bool) -> String -> Parser c (c, Char)
satisfyInternal newc cond emsg = PParse(\(coord, str) ->
    case str of
        [] -> PFail coord emsg
        (c:cs) -> if cond c then POk (coord, c) (newc coord c, cs)
                            else PFail coord emsg
    )

--Definizioni utili

--Sistema di coordinate predefinito, viene stampato con la forma: [file:line:col]
data StdCoord = Coord String Int Int
type StdParser = Parser StdCoord

instance Show StdCoord where
    show (Coord file line col) =
        "[" ++ file ++ ":" ++ show line ++ ":" ++ show col ++ "]"
dummyStdCoord :: StdCoord
dummyStdCoord = Coord "" 0 0

stdcoordNewc :: StdCoord -> Char -> StdCoord
stdcoordNewc (Coord file line col) char = --TODO: Come si trattano i caratteri a più celle?
    case char of
        '\n' -> Coord file (line+1) 1
        _ -> Coord file line (col+1)

--satisfy con StdCoord
stdSatisfy :: (Char -> Bool) -> String -> StdParser (StdCoord, Char)
stdSatisfy = satisfyInternal stdcoordNewc

--raccoglie il carattere specificato
thisChar :: Char -> StdParser (StdCoord, Char)
thisChar char = stdSatisfy (char==) ("Expected character: \'" ++ char : '\'' : [])
--raccoglie uno dei caratteri specificati
anyChar :: [Char] -> StdParser (StdCoord, Char)
anyChar chars = stdSatisfy (\c -> any (c==) chars) ("Expected one of these chars: \"" ++ chars ++ "\"")

--alcuni parser utili
asciiAlphaLower, asciiAlphaUpper, digit, asciiAlphaNumeric, whiteSpace :: StdParser (StdCoord, Char)
asciiAlphaLower   = anyChar "abcdefghijklmnopqrstuvwxyz"
asciiAlphaUpper   = anyChar "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
digit             = anyChar "01234567890"
asciiAlphaNumeric = asciiAlphaLower <|| asciiAlphaUpper <|| digit
whiteSpace        = stdSatisfy isSpace "Expected a whitespace"
