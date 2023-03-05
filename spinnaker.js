class RealWorld_ { constructor(){} }
class Tup0 { constructor(){} }
class Tup2 {
    constructor(x0, x1) {
        this[0] = x0;
        this[1] = x1;
    }
}
class Tup3 {
    constructor(x0, x1, x2) {
        this[0] = x0;
        this[1] = x1;
        this[2] = x2;
    }
}
class Tup4 {
    constructor(x0, x1, x2, x3) {
        this[0] = x0;
        this[1] = x1;
        this[2] = x2;
        this[3] = x3;
    }
}

function _addInt(a, b) {
    return a + b;
}
function _subInt(a, b) {
    return a - b;
}
function _mulInt(a, b) {
    return a * b;
}
function _divInt(a, b) {
    return Math.floor(a / b); //TODO euclidean division
}
function _equInt (a, b) {
    if (a === b) {
        return 1;
    } else {
        return 0;
    }
}
function _neqInt (a, b) {
    if (a !== b) {
        return 1;
    } else {
        return 0;
    }
}
function _leqInt (a, b) {
    if (a <= b) {
        return 1;
    } else {
        return 0;
    }
}
function _greInt (a, b) {
    if (a > b) {
        return 1;
    } else {
        return 0;
    }
}

function _addFlt(a, b) {
    return a + b;
}
function _subFlt(a, b) {
    return a - b;
}
function _mulFlt(a, b) {
    return a * b;
}
function _divFlt(a, b) {
    return a / b;
}
function _equFlt (a, b) {
    if (a === b) {
        return 1;
    } else {
        return 0;
    }
}
function _neqFlt (a, b) {
    if (a !== b) {
        return 1;
    } else {
        return 0;
    }
}
function _leqFlt (a, b) {
    if (a <= b) {
        return 1;
    } else {
        return 0;
    }
}
function _greFlt (a, b) {
    if (a === b) {
        return 1;
    } else {
        return 0;
    }
}

function _floorFlt(a) {
    return Math.floor(a);
}
function _convItoF(a) {
    return a;
}

function _convItoC(a) {
    return String.fromCharCode(a);
}
function _convCtoI(a) {
    return a.charCodeAt();
}

let chrbuffer = ""
function _putChr(c,rw) {
    if (c === '\n') {
        console.log(chrbuffer);
        chrbuffer = "";
    } else {
        chrbuffer = chrbuffer + c;
    }
    return rw;
}

//TODO _putChr serio, _getChr, _isEOF
function _exit(a) {
    throw new Error('Program exited');
    return a;
}
