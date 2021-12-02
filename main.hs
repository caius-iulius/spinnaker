-- TODO: put v | Cons x Nil -> ... non funziona, va scritto put v | Cons x (Nil) -> ... . FIX
-- TODO: Parsing dei commenti
-- TODO: Parsing dei datatype
-- TODO: Se voglio considerare questa la specifica formale della grammatica devo aggiungere molti commenti

import System.IO
import System.Environment
import MPCL
import HIRDefs

labelFirst = thisChar '_' <|| alphaLower
capitalLabelFirst = alphaCapital
labelChar = thisChar '_' <|| alphanumeric
tailDigit = thisChar '_' <|| numeric

opChar = anyChar ":!#$%&*+/-<=>?@\\^|."

inArrow = "->"
putSeparator = "|"
lambdaInit = "\\"
commentStart = "/*"
commentEnd = "*/"

validSymbols = [inArrow, putSeparator, lambdaInit, commentStart, commentEnd]

keywords = ["let", "put", "_", "def", "pub", "type", "and"]

-- TODO questo dovrà anche riconoscere i commenti
skipUseless = munch whiteSpace
getLabelText = do {
    skipUseless;
    (c, f) <- labelFirst;
    others <- munch labelChar;
    quotes <- munch $ thisChar '\'';
    return (c, f:map snd (others ++ quotes))
}

getKeyword = do {
    (c, s) <- getLabelText;
    if elem s keywords
    then return (c, s)
    else pfail "Expected keyword"
}

getLabel = do {
    (c, s) <- getLabelText;
    if elem s keywords
    then pfail "Expected label"
    else return (c, s)
}

getCapitalLabel = do {
    skipUseless;
    (c, f) <- capitalLabelFirst;
    others <- munch labelChar;
    return (c, f:map snd others)
}

getInteger = do {
    skipUseless;
    (coord, firsts) <- describeError "Expected either a '-' or a digit in an integer" $ do {
        (c, first) <- numeric;
        return (c, first:[])
    } <|| do {
        (c, sign) <- thisChar '-';
        (_, first) <- numeric;
        return (c, sign:first:[])
    };
    others <- munch tailDigit;
    return (coord, read $ filter ('_' /=) $ (firsts ++ map snd others))
}

getFloat = do {
    skipUseless;
    (coord, firsts) <- describeError "Expected either a '-' or a digit in a float" $ do {
        (c, first) <- numeric;
        return (c, first:[])
    } <|| do {
        (c, sign) <- thisChar '-';
        (_, first) <- numeric;
        return (c, sign:first:[])
    };
    othersFirst <- munch tailDigit;
    thisChar '.';
    othersSecond <- munch1 tailDigit;
    return (coord, read $ filter ('_' /=) $ (firsts ++ map snd othersFirst ++ "." ++ map snd othersSecond))
}
getLiteral = describeError "Expected literal" $ do {
    (c, f) <- getFloat;
    return $ (c, LitFloating f)
} <|| do {
    (c, i) <- getInteger;
    return $ (c, LitInteger i)
}

getOperatorText = do {
    skipUseless;
    chars <- munch1 opChar;
    return (fst $ head $ chars, map snd chars)
}

getOperator = do {
    (c, s) <- getOperatorText;
    if elem s validSymbols
    then pfail "Expected operator"
    else return (c, s)
}

thisSyntaxElem test = describeError ("Expected keyword or symbol '" ++ test ++ "'") $ do {
    (c, s) <- getKeyword <|| getOperatorText; --TODO: Forse invece questo, ma taglia fuori invece "=", che è un operatore usato anche per le assegnazioni: do {(c', s') <- getOperatorText; if elem s' validSymbols then return (c', s') else pfail "thisSyntaxElem"};
    if s == test then return (c, s) else pfail ""
}

discard p = p >> return ()

-- Analisi semantica
getPatternTerm = describeError "Expected pattern term" $ do {
    (c, l) <- getLiteral;
    return (c, PatLiteral l)
} <|| do {
    (c, l) <- getLabel;
    return (c, PatLabel l)
} <|| do {
    (c, k) <- getKeyword;
    if k == "_" then return (c, PatWildcard)
    else pfail ""
} <|| do {
    skipUseless;
    (c, _) <- thisChar '(';
    m <- sepBy getPatternExpr (skipUseless >> thisChar ',');
    skipUseless;
    require $ thisChar ')';

    if length m == 1
    then return $ head m
    else return (c, PatTuple m)
}

getPatternExpr = do{
    (c, cons) <- getCapitalLabel;
    args <- munch getPatternTerm;
    return (c, PatVariant cons args)
} <|| getPatternTerm

getTerm = describeError "Expected term" $ do { -- Literal
    (c, l) <- getLiteral;
    return (c, ExprLiteral l)
} <|| do { -- Label
    (c, l) <- getLabel;
    return (c, ExprLabel l)
} <|| do { -- CapitalLabel, identifica la variante, in futuro anche modulo (quando c'è il punto dopo)
    (c, l) <- getCapitalLabel;
    return (c, ExprLabel l)
} <|| do { -- '(' META ',' ... ',' META ')' o '(' META ')'
    skipUseless;
    (c, _) <- thisChar '(';
    m <- sepBy getMeta (skipUseless >> thisChar ',');
    skipUseless;
    require $ thisChar ')';
    if length m == 1
    then return $ head m
    else return (c, ExprTuple m)
}

getExpr = do {
    skipUseless;
    (c, _) <- thisChar '\\';
    curriedargs <- sepBy1 getPatternTerm (skipUseless >> thisChar ','); --[Pattern]
    skipUseless;
    require $ thisChar '{';
    internal <- getMeta; --Expr
    skipUseless;
    require $ thisChar '}';
    return $ foldr (\p e-> (fst p, ExprLambda p e)) internal curriedargs
} <|| do { --FCall e Label nel caso che ce ne sia una
    terms <- munch1 getTerm;
    return $ foldl1 (\t1 t2 -> (fst t1, ExprFCall t1 t2)) terms
} 

getMeta = getLet <|| getPut <|| do { --EXPR OP META
    expr <- getExpr;
    (opc, op) <- getOperator;
    meta <- require getMeta;
    return (opc, ExprFCall (opc, ExprFCall (opc, ExprLabel op) expr) meta) 
} <|| getExpr

getLet = do
    (c, _) <- thisSyntaxElem "let"
    require $ do {
        p <- require getPatternExpr;
        thisSyntaxElem "=";
        val <- getMeta;
        thisSyntaxElem "->";
        expr <- getMeta;
        return (c, ExprPut val [(p, expr)])
    }

getBranch = do
    skipUseless;
    thisChar '|';
    require $ do {
        p <- require getPatternExpr;
        thisSyntaxElem "->";
        expr <- getMeta;
        return (p, expr)
    }

getPut = do
    (c, _) <- thisSyntaxElem "put"
    require $ do {
        val <- getMeta;
        branches <- munch1 getBranch;
        return (c, ExprPut val branches)
    }

getDefinition = do {
    label <- describeError "Expected a label or a parenthesisised operator" $ do {skipUseless; thisChar '('; op <- getOperator; skipUseless; thisChar ')'; return op}
             <|| getLabel;
    skipUseless;
    thisChar '=';
    meta <- getMeta;
    return (fst label, snd label, meta)
}

getDefinitions = do {
    (c, _) <- thisSyntaxElem "def";
    defs <- sepBy1 getDefinition $ thisSyntaxElem "and";
    return $ ProgDefs defs
}

--Entry point (da modificare)
getProgram = do {
    res <- munch getDefinitions;
    skipUseless;
    reachedEof;
    return res
}

{-main = do {
    putStr ":= ";
    input <- getLine;
    putStrLn $ show $ parse getDefinitions (Coord "in" 1 1, input);
    return ()
}-}


main = do {
    args <- getArgs;
    handle <- openFile (head args) ReadMode;
    contents <- hGetContents handle;
    putStrLn "Program:";
    putStrLn contents;
    putStrLn "Parsed:";
    print $ parse getProgram (Coord (head args) 1 1, contents)
}
