-- TODO FORSE: Parsing dei commenti multilinea
-- TODO: Se voglio considerare questa la specifica formale della grammatica devo aggiungere molti commenti
module Parser where
import Data.Char
import GHC.Unicode
import MPCL
import TypingDefs(DataType(DataNOTHING), TyQuant(TyQuant), Kind(KindNOTHING))
import HLDefs
import SyntaxDefs

labelFirst = thisChar '_' <|| asciiAlphaLower
capitalLabelFirst = asciiAlphaUpper
labelChar = thisChar '_' <|| asciiAlphaNumeric
tailDigit = thisChar '_' <|| digit

opChar = anyChar ":!$%&*+/-<=>?@\\^|~."

validSymbols = ["->", "|", "\\", "."]

keywords = ["_", "put", "let", "if", "then", "else", "pub", "and", "forall", "def", "data", "typesyn", "use", "mod"]

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
getListPat = skipUseless >> (thisChar '[' >>= \(c, _) -> require $ (skipUseless >> thisChar ']' >> return (c, Nothing, SynPatListNil)) <|| do {
    es <- sepBy1 getPatternExpr (skipUseless >> thisChar ',');
    final <- option (c, Nothing, SynPatListNil) (thisSyntaxElem "|" >> require getPatternExpr);
    skipUseless;
    thisChar ']';
    return (c, Nothing, SynPatListConss es final)
})

getPatternTerm = describeError "Expected pattern term" $ do {
    (c, l) <- getLiteral;
    return (c, Nothing, SynPatLiteral l)
} <|| do {
    (c, l) <- getLabel;
    return (c, Just l, SynPatWildcard)
} <|| do {
    (c, l) <- getPathCapitalLabel;
    return (c, Nothing, SynPatVariant l [])
} <|| do {
    (c, k) <- getKeyword;
    if k == "_" then return (c, Nothing, SynPatWildcard)
    else pfail ""
} <|| getListPat
  <|| do {
    skipUseless;
    (c, _) <- thisChar '(';
    m <- sepBy getPatternExpr (skipUseless >> thisChar ',');
    skipUseless;
    require $ thisChar ')';

    if length m == 1
    then return $ head m
    else return (c, Nothing, SynPatTuple m)
}

getPatternExpr = do{
    (c, cons) <- getPathCapitalLabel;
    args <- munch getPatternTerm;
    return (c, Nothing, SynPatVariant cons args)
} <|| getPatternTerm

-- Parser vari per le espressioni
getListExpr = skipUseless >> (thisChar '[' >>= \(c, _) -> require $ (skipUseless >> thisChar ']' >> return (c, SynExprListNil)) <|| do {
    es <- sepBy1 getMeta (skipUseless >> thisChar ',');
    final <- option (c, SynExprListNil) (thisSyntaxElem "|" >> require getMeta);
    skipUseless;
    thisChar ']';
    return (c, SynExprListConss es final)
})

getTerm = describeError "Expected term" $ do { --String
    (c, s) <- getString;
    return (c, SynExprListConss (map (\char->(c, SynExprLiteral $ LitInteger $ ord char)) s) (c, SynExprListNil))
} <|| do { -- Literal
    (c, l) <- getLiteral;
    return (c, SynExprLiteral l)
} <|| do { -- Label
    (c, l) <- getPathLabel;
    return (c, SynExprLabel l)
} <|| do { -- CapitalLabel, identifica la variante, in futuro anche modulo (quando c'è il punto dopo)
    (c, l) <- getPathCapitalLabel;
    return (c, SynExprConstructor l)
} <|| getListExpr
  <|| getInlineUse
  <|| do { -- '(' META ',' ... ',' META ')' o '(' META ')'
    skipUseless;
    (c, _) <- thisChar '(';
    m <- sepBy getMeta (skipUseless >> thisChar ',');
    skipUseless;
    require $ thisChar ')';
    if length m == 1
    then return $ head m
    else return (c, SynExprTuple m)
}

getExpr = do { --FCall e Label nel caso che ce ne sia una
    terms <- munch1 getTerm;
    return $ let (c,_) = head terms in
        foldl1 (\t1 t2 -> (c, SynExprApp t1 t2)) terms
}

getMeta = getLambda <|| getIfThenElse <|| getLet <|| getPut <|| do { --EXPR OP META
    expr <- getExpr;
    (opc, op) <- getOperator;
    meta <- require getMeta;
    return (opc, SynExprApp (opc, SynExprApp (opc, SynExprLabel $ Path [] op) expr) meta)
} <|| getExpr

getLet = do
    (c, _) <- thisSyntaxElem "let"
    require $ do {
        p <- require getPatternExpr;
        thisSyntaxElem "=";
        val <- getMeta;
        thisSyntaxElem "->";
        expr <- getMeta;
        return (c, SynExprPut val [(p, expr)])
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
        return (c, SynExprPut val branches)
    }

getLambda = do {
    (c, _) <- thisSyntaxElem "\\";
    require $ do{
        curriedargs <- sepBy1 getPatternExpr (skipUseless >> thisChar ','); --[Pattern] --TODO: o patternexpr divisi da virgole o sequenza di patternterm
        skipUseless;
        thisSyntaxElem "->";
        internal <- getMeta; --Expr
        skipUseless;
        return $ foldr (\p e-> ((\(c',_,_)->c') p, SynExprLambda p e)) internal curriedargs
    }
}

getIfThenElse = do {
    (c, _) <- thisSyntaxElem "if";
    require $ do {
        cond <- getMeta;
        thisSyntaxElem "then";
        iftrue <- getMeta;
        thisSyntaxElem "else";
        iffalse <- getMeta;
        return (c, SynExprIfThenElse cond iftrue iffalse)
    }
}

getInlineUse = do {
    path <- getPath;
    if length path == 0 then pfail "Expected at least a module name" else return ();
    skipUseless;
    thisChar '(';
    m <- require getMeta;
    skipUseless;
    require $ thisChar ')';
    let lablonlypath = map snd path in
        return $ (fst $ head path, SynExprInlineUse (Path (init lablonlypath) (last lablonlypath)) m)
}

-- Parser globali
getVisibility = option Private (thisSyntaxElem "pub" >> return Public)

-- Parser per i tipi
getTypeVar = getLabel --TODO: Anche i tipi higher-order? magari è sintassi diversa

-- TODO: TypeMeta, test typeexpr
getTypeTerm = do { --Tipo quantifier
    (c, l) <- getLabel;
    return (c, SynTypeExprQuantifier l)
} <|| do { --Tipo data
    (c, l) <- getPathCapitalLabel;
    return (c, SynTypeExprName l)
} <|| do {
    skipUseless;
    (c, _) <- thisChar '(';
    types <- sepBy getTypeMeta (skipUseless >> thisChar ',');
    skipUseless;
    require $ thisChar ')';
    if length types == 1
    then return $ head types
    else return (c, SynTypeExprTuple types)
}

getTypeExpr = do {
    terms <- munch1 getTypeTerm;
    return $ let f@(c,_) = head terms in
        (c, SynTypeExprApp f (tail terms))
} <|| getTypeTerm


getTypeMeta = do {
    e <- getTypeExpr;
    (c, _) <- thisSyntaxElem "->";
    m <- require getTypeMeta;
    return (c, SynTypeExprApp (c, SynTypeExprName $ Path [] "->") [e, m])
} <|| getTypeExpr

getTyScheme = do {
    (c, _) <- thisSyntaxElem "forall";
    require $ do {
        typevars <- munch getTypeVar; -- TODO
        thisSyntaxElem ".";
        m <- getTypeMeta;
        return (c, map snd typevars, m)
    }
} <|| do {
    m <- getTypeMeta;
    return (fst m, [], m)
}

-- Parser per le definizioni
getValDefinition = require $ do {
    visib <- getVisibility;
    (c, label) <- getLabel;
    typehint <- option Nothing (thisSyntaxElem ":" >> (require $ getTyScheme >>= return . Just));
    thisSyntaxElem "=";
    meta <- getMeta;
    return $ SynValDef c visib label typehint meta
}
getValDefinitions = do {
    thisSyntaxElem "def";
    defs <- sepBy1 getValDefinition (thisSyntaxElem "and");
    return $ ModValGroup defs
}

-- Parser vari per datatype
getVariant = do {
    (c, label) <- getCapitalLabel;
    tyexprs <- munch getTypeTerm;
    return $ SynDataVariant c label tyexprs
}
getDataDefinition = require $ do {
    visib <- getVisibility;
    (c, label) <- getCapitalLabel;
    typevars <- munch getTypeVar; -- TODO 
    thisSyntaxElem "=";
    variants <- sepBy getVariant $ thisSyntaxElem "|";
    return $  SynDataDef c visib label (map snd typevars) variants --TODO quantificatore iniziale?
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

getTypeSyn = do {
    (c, _) <- thisSyntaxElem "typesyn";
    require $ do {
        visib <- getVisibility;
        (_, label) <- getCapitalLabel;
        qs <- munch getLabel;
        thisSyntaxElem "=";
        te <- getTypeMeta;
        return $ ModTypeSyn c visib label (map snd qs) te
    }
}
getModuleInnerDefs = do {
    res <- munch (getValDefinitions <|| getDataDefinitions <|| getTypeSyn <|| getUse <|| getModuleDef);
    return $ Module res
}
--Entry point (da modificare)
getProgram = do {
    prog <- getModuleInnerDefs;
    skipUseless;
    reachedEof;
    return prog
}
