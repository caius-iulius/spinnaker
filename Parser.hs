-- TODO FORSE: Parsing dei commenti multilinea
-- TODO: Se voglio considerare questa la specifica formale della grammatica devo aggiungere molti commenti
module Parser where
import GHC.Unicode
import MPCL
import TypingDefs(DataType(DataNOTHING), TyQuant(TyQuant), Kind(KindNOTHING))
import HLDefs
import HIRDefs

labelFirst = thisChar '_' <|| asciiAlphaLower
capitalLabelFirst = asciiAlphaUpper
labelChar = thisChar '_' <|| asciiAlphaNumeric
tailDigit = thisChar '_' <|| digit

opChar = anyChar ":!$%&*+/-<=>?@\\^|."

inArrow = "->"
putSeparator = "|"
lambdaInit = "\\"
fieldDot = "."

validSymbols = [inArrow, putSeparator, lambdaInit, fieldDot]

keywords = ["_", "put", "let", "pub", "and", "def", "data", "use", "mod"]

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

getCapitalLabel = do {
    skipUseless;
    (c, f) <- capitalLabelFirst;
    others <- munch labelChar;
    quotes <- munch $ thisChar '\'';
    return (c, f:map snd (others++quotes))
}

getInteger = do {
    skipUseless;
    (coord, firsts) <- describeError "Expected either a '-' or a digit in an integer" $ do {
        (c, first) <- digit;
        return (c, first:[])
    } <|| do {
        (c, sign) <- thisChar '-';
        (_, first) <- digit;
        return (c, sign:first:[])
    };
    others <- munch tailDigit;
    return (coord, read $ filter ('_' /=) $ (firsts ++ map snd others))
}

getFloat = do {
    skipUseless;
    (coord, firsts) <- describeError "Expected either a '-' or a digit in a float" $ do {
        (c, first) <- digit;
        return (c, first:[])
    } <|| do {
        (c, sign) <- thisChar '-';
        (_, first) <- digit;
        return (c, sign:first:[])
    };
    othersFirst <- munch tailDigit;
    thisChar '.';
    othersSecond <- munch1 tailDigit;
    return (coord, read $ filter ('_' /=) $ (firsts ++ map snd othersFirst ++ "." ++ map snd othersSecond))
}

getEscape = do {
    (c, _) <- thisChar '\\';
    char <- (thisChar 'n' >> return '\n') <|| (thisChar '"' >> return '"'); --TODO Altri escape
    return (c, char)
}

getString = do {
    skipUseless;
    (c, _) <- thisChar '\"';
    chars <- munch (difference (stdSatisfy isPrint "") (thisChar '"' <|| thisChar '\\') <|| getEscape <|| whiteSpace);
    require $ thisChar '\"';
    return (c, map snd chars)
}

getLiteral = describeError "Expected literal" $ do {
    (c, f) <- getFloat;
    return $ (c, LitFloating f)
} <|| do {
    (c, i) <- getInteger;
    return $ (c, LitInteger i)
} {- <|| do {
    (c, s) <- getString;
    return $ (c, LitString s)
} -}

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

getLabel = do {
    skipUseless;
    thisChar '(';
    op <- getOperator;
    skipUseless;
    require $ describeError "Expected closing paren after operator section" $ thisChar ')';
    return op
} <|| do {
    (c, s) <- getLabelText;
    if elem s keywords
    then pfail "Expected label"
    else return (c, s)
}

-- Raccoglie una keyword oppure un simbolo composto dai caratteri di operatore
thisSyntaxElem test = describeError ("Expected keyword or symbol '" ++ test ++ "'") $ do {
    (c, s) <- getKeyword <|| getOperatorText;
    if s == test then return (c, s) else pfail ""
}

getModName = getCapitalLabel

getPath = munch $ do{l <- getModName; thisSyntaxElem "."; return l}

getPathLabel = do {
    path <- getPath;
    (c, label) <- getLabel;
    return (if length path == 0 then c else fst $ head path, Path (map snd $ path) label)
}

getPathCapitalLabel = do {
    path <- getPath;
    (c, label) <- getCapitalLabel;
    return (if length path == 0 then c else fst $ head path, Path (map snd $ path) label)
}

-- Analisi semantica

-- Parser vari per pattern
getPatternTerm = describeError "Expected pattern term" $ do {
    (c, l) <- getLiteral;
    return (c, Nothing, PatLiteral l)
} <|| do {
    (c, l) <- getLabel;
    return (c, Just l, PatWildcard)
} <|| do {
    (c, l) <- getPathCapitalLabel;
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
    (c, cons) <- getPathCapitalLabel;
    args <- munch getPatternTerm;
    return (c, Nothing, PatVariant cons args)
} <|| getPatternTerm

-- Parser vari per le espressioni
getTerm = describeError "Expected term" $ do { -- Literal
    (c, l) <- getLiteral;
    return (c, DataNOTHING, ExprLiteral l)
} <|| do { -- Label
    (c, l) <- getPathLabel;
    return (c, DataNOTHING, ExprLabel l)
} <|| do { -- CapitalLabel, identifica la variante, in futuro anche modulo (quando c'è il punto dopo)
    (c, l) <- getPathCapitalLabel;
    return (c, DataNOTHING, ExprConstructor l)
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
    (c, _) <- thisSyntaxElem "\\";
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
    return $ let (c,_,_) = head terms in
        foldl1 (\t1 t2 -> (c, DataNOTHING, ExprApp t1 t2)) terms
}

getMeta = getLet <|| getPut <|| do { --EXPR OP META
    expr <- getExpr;
    (opc, op) <- getOperator;
    meta <- require getMeta;
    return (opc, DataNOTHING, ExprApp (opc, DataNOTHING, ExprApp (opc, DataNOTHING, ExprLabel $ Path [] op) expr) meta)
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
    thisSyntaxElem "|";
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

-- Parser globali
getVisibility = option Private (thisSyntaxElem "pub" >> return Public)
-- Parser per le definizioni
getValDefinition = do {
    visib <- getVisibility;
    (c, label) <- getLabel;
    thisSyntaxElem "=";
    meta <- getMeta;
    return $ (visib, ValDef c label meta)
}
getValDefinitions = do {
    thisSyntaxElem "def";
    defs <- sepBy1 getValDefinition (thisSyntaxElem "and");
    return $ ModValGroup defs
}

-- Parser per i tipi
getTypeVar = getLabel --TODO: Anche i tipi higher-order? magari è sintassi diversa

-- TODO: TypeMeta, test typeexpr
getTypeTerm = do { --Tipo quantifier
    (c, l) <- getLabel;
    return (c, TypeExprQuantifier l)
} <|| do { --Tipo data
    (c, l) <- getPathCapitalLabel;
    return (c, TypeExprName l)
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
    terms <- munch1 getTypeTerm;
    return $ let (c,_) = head terms in
        foldl1 (\t1 t2 -> (c, TypeExprApp t1 t2)) terms
} <|| getTypeTerm


getTypeMeta = do {
    e <- getTypeExpr;
    (c, _) <- thisSyntaxElem "->";
    m <- require getTypeMeta;
    return (c, TypeExprApp (c, TypeExprApp (c, TypeExprName $ Path [] "->") e) m)
} <|| getTypeExpr

-- Parser vari per datatype
getVariant = do {
    (c, label) <- getCapitalLabel;
    tyexprs <- munch getTypeTerm;
    return $ DataVariant c label (map (\e->(DataNOTHING,e)) tyexprs)
}
getDataDefinition = do {
    visib <- getVisibility;
    (c, label) <- getCapitalLabel;
    typevars <- munch getTypeVar; -- TODO 
    thisSyntaxElem "=";
    variants <- sepBy getVariant $ thisSyntaxElem "|";
    return $ DataDef c visib label (map (\(c, tv)->(tv, (TyQuant 0 KindNOTHING))) typevars) variants --TODO quantificatore iniziale?
}

getDataDefinitions = do {
    thisSyntaxElem "data";
    defs <- sepBy1 getDataDefinition (thisSyntaxElem "and");
    return $ ModDataGroup defs
}

getUse = do {
    (c, _) <- thisSyntaxElem "use";
    require $ do {
        visib <- getVisibility;
        (_, path) <- getPathCapitalLabel;
        return (ModUse c visib path)
    }
}

getModuleDef = do {
    (c, _) <- thisSyntaxElem "mod";
    require $ do {
        visib <- getVisibility;
        (_, label) <- getCapitalLabel;
        skipUseless;
        thisChar '{';
        mod <- getModuleInnerDefs;
        skipUseless;
        thisChar '}';
        return $ ModMod c visib label mod
    }
}

getModuleInnerDefs = do {
    res <- munch (getValDefinitions <|| getDataDefinitions <|| getUse <|| getModuleDef);
    return $ Module res
}
--Entry point (da modificare)
getProgram = do {
    prog <- getModuleInnerDefs;
    skipUseless;
    reachedEof;
    return prog
}
