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
function _remInt(a, b) {
    return a % b;
}
function _equInt (a, b) {
    return a === b;
}
function _neqInt (a, b) {
    return a !== b;
}
function _leqInt (a, b) {
    return a <= b;
}
function _greInt (a, b) {
    return a > b;
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
    return a === b;
}
function _neqFlt (a, b) {
    return a !== b;
}
function _leqFlt (a, b) {
    return a <= b;
}
function _greFlt (a, b) {
    return a > b;
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
    process.exit(0);
    return a;
}
