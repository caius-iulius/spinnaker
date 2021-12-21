-- TODO FORSE: Parsing dei commenti multilinea
-- TODO: Se voglio considerare questa la specifica formale della grammatica devo aggiungere molti commenti
module Parser where

import MPCL
import HIRDefs
import TypingDefs(DataType(DataNOTHING))

labelFirst = thisChar '_' <|| alphaLower
capitalLabelFirst = alphaCapital
labelChar = thisChar '_' <|| alphanumeric
tailDigit = thisChar '_' <|| numeric

opChar = anyChar ":!$%&*+/-<=>?@\\^|."

inArrow = "->"
putSeparator = "|"
lambdaInit = "\\"
commentStart = "/*"
commentEnd = "*/"

validSymbols = [inArrow, putSeparator, lambdaInit, commentStart, commentEnd]

keywords = ["let", "put", "_", "def", "and", "data", "pub", "type", "and"]

lineComment = do {
    thisChar '#';
    munch (stdSatisfy (not . ('\n'==)) "");
}

skipUseless = do {
    munch (discard whiteSpace <|| discard lineComment);
}
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

-- Raccoglie una keyword oppure un simbolo composto dai caratteri di operatore
thisSyntaxElem test = describeError ("Expected keyword or symbol '" ++ test ++ "'") $ do {
    (c, s) <- getKeyword <|| getOperatorText;
    if s == test then return (c, s) else pfail ""
}

discard p = p >> return ()

-- Analisi semantica

-- Parser vari per pattern
getPatternTerm = describeError "Expected pattern term" $ do {
    (c, l) <- getLiteral;
    return (c, Nothing, PatLiteral l)
} <|| do {
    (c, l) <- getLabel;
    return (c, Just l, PatWildcard)
} <|| do {
    (c, l) <- getCapitalLabel;
    return (c, Nothing, PatVariant l [])
} <|| do {
    (c, k) <- getKeyword;
    if k == "_" then return (c, Nothing, PatWildcard)
    else pfail ""
} <|| do {
    skipUseless;
    (c, _) <- thisChar '(';
    m <- sepBy getPatternExpr (skipUseless >> thisChar ',');
    skipUseless;
    require $ thisChar ')';

    if length m == 1
    then return $ head m
    else return (c, Nothing, PatTuple m)
}

getPatternExpr = do{
    (c, cons) <- getCapitalLabel;
    args <- munch getPatternTerm;
    return (c, Nothing, PatVariant cons args)
} <|| getPatternTerm

-- Parser vari per le espressioni
getTerm = describeError "Expected term" $ do { -- Literal
    (c, l) <- getLiteral;
    return (c, DataNOTHING, ExprLiteral l)
} <|| do { -- Label
    (c, l) <- getLabel;
    return (c, DataNOTHING, ExprLabel l)
} <|| do { -- CapitalLabel, identifica la variante, in futuro anche modulo (quando c'è il punto dopo)
    (c, l) <- getCapitalLabel;
    return (c, DataNOTHING, ExprLabel l)
} <|| do { -- '(' META ',' ... ',' META ')' o '(' META ')'
    skipUseless;
    (c, _) <- thisChar '(';
    m <- sepBy getMeta (skipUseless >> thisChar ',');
    skipUseless;
    require $ thisChar ')';
    if length m == 1
    then return $ head m
    else return (c, DataNOTHING, ExprTuple m)
}

getExpr = do {
    skipUseless;
    (c, _) <- thisChar '\\';
    require $ do{
        curriedargs <- sepBy1 getPatternTerm (skipUseless >> thisChar ','); --[Pattern]
        skipUseless;
        thisChar '{';
        internal <- getMeta; --Expr
        skipUseless;
        thisChar '}';
        return $ foldr (\p e-> ((\(c',_,_)->c') p, DataNOTHING, ExprLambda p e)) internal curriedargs
    }
} <|| do { --FCall e Label nel caso che ce ne sia una
    terms <- munch1 getTerm;
    return $ foldl1 (\t1 t2 -> ((\(c,_,_)->c) t1, DataNOTHING, ExprFCall t1 t2)) terms
} 

getMeta = getLet <|| getPut <|| do { --EXPR OP META
    expr <- getExpr;
    (opc, op) <- getOperator;
    meta <- require getMeta;
    return (opc, DataNOTHING, ExprFCall (opc, DataNOTHING, ExprFCall (opc, DataNOTHING, ExprLabel op) expr) meta)
} <|| getExpr

getLet = do
    (c, _) <- thisSyntaxElem "let"
    require $ do {
        p <- require getPatternExpr;
        thisSyntaxElem "=";
        val <- getMeta;
        thisSyntaxElem "->";
        expr <- getMeta;
        return (c, DataNOTHING, ExprPut val [(p, expr)])
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
        return (c, DataNOTHING, ExprPut val branches)
    }

-- Parser per le definizioni
getValDefinition = do {
    (c, label) <- describeError "Expected a label or a parenthesisised operator" $ do {skipUseless; thisChar '('; op <- getOperator; skipUseless; thisChar ')'; return op}
             <|| getLabel;
    thisSyntaxElem "=";
    meta <- getMeta;
    return $ ValDef c label meta
}
getValDefinitions = do {
    thisSyntaxElem "def";
    defs <- sepBy1 getValDefinition (thisSyntaxElem "and");
    return $ Right defs
}

-- Parser per i tipi
getTypeVar = getLabel --TODO: Anche i tipi higher-order? magari è sintassi diversa

-- TODO: TypeMeta, test typeexpr
getTypeTerm = do { --Tipo quantifier
    (c, l) <- getLabel;
    return (c, TypeExprQuantifier l)
} <|| do { --Tipo concreto
    (c, l) <- getCapitalLabel;
    return (c, TypeExprTypeApp l [])
} <|| do {
    skipUseless;
    (c, _) <- thisChar '(';
    types <- sepBy getTypeMeta (skipUseless >> thisChar ',');
    skipUseless;
    require $ thisChar ')';
    if length types == 1
    then return $ head types
    else return (c, TypeExprTuple types)
}

getTypeExpr = do {
    (c, l) <- getLabel <|| getCapitalLabel;
    args <- munch getTypeTerm;
    return (c, TypeExprTypeApp l args)
} <|| getTypeTerm


getTypeMeta = do {
    e <- getTypeExpr;
    (c, _) <- thisSyntaxElem "->";
    m <- require getTypeMeta;
    return (c, TypeExprFun e m)
} <|| getTypeExpr

-- Parser vari per datatype
getVariant = do {
    (c, label) <- getCapitalLabel;
    tyexprs <- munch getTypeTerm;
    return $ DataVariant c label (map (\e->(DataNOTHING,e)) tyexprs)
}

getDataDefinition = do { --pfatal "DATA DEFINITIONS NOT IMPLEMENTED"
    (c, _) <- thisSyntaxElem "data";
    (_, label) <- getCapitalLabel;
    typevars <- munch getTypeVar; -- TODO 
    thisSyntaxElem "=";
    variants <- sepBy1 getVariant $ thisSyntaxElem "|";
    return $ Left $ DataDef c label (map (\(c, tv)->(0, tv)) typevars) variants --TODO quantificatore iniziale?
}

listEitherDefToTup [] = ([], [])
listEitherDefToTup (Left ddef:defs) =
    let (ddefs, vdefs) = listEitherDefToTup defs in (ddef:ddefs, vdefs)
listEitherDefToTup (Right vdef:defs) =
    let (ddefs, vdefs) = listEitherDefToTup defs in (ddefs, vdef:vdefs)
--Entry point (da modificare)
getProgram = do {
    res <- munch (getValDefinitions <|| getDataDefinition);
    skipUseless;
    reachedEof;
    let (ddefs, vdefs) = listEitherDefToTup res
        in return $ Program ddefs vdefs
}
