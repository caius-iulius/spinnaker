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

function spinnaker_addInt(a, b) {
    return a + b;
}
function spinnaker_subInt(a, b) {
    return a - b;
}
function spinnaker_mulInt(a, b) {
    return a * b;
}
function spinnaker_divInt(a, b) {
    return Math.trunc(a / b); //TODO euclidean division
}
function spinnaker_remInt(a, b) {
    return a % b;
}
function spinnaker_equInt (a, b) {
    return a === b;
}
function spinnaker_neqInt (a, b) {
    return a !== b;
}
function spinnaker_leqInt (a, b) {
    return a <= b;
}
function spinnaker_greInt (a, b) {
    return a > b;
}

function spinnaker_addFlt(a, b) {
    return a + b;
}
function spinnaker_subFlt(a, b) {
    return a - b;
}
function spinnaker_mulFlt(a, b) {
    return a * b;
}
function spinnaker_divFlt(a, b) {
    return a / b;
}
function spinnaker_equFlt (a, b) {
    return a === b;
}
function spinnaker_neqFlt (a, b) {
    return a !== b;
}
function spinnaker_leqFlt (a, b) {
    return a <= b;
}
function spinnaker_greFlt (a, b) {
    return a > b;
}

function spinnaker_floorFlt(a) {
    return Math.floor(a);
}
function spinnaker_convItoF(a) {
    return a;
}

function spinnaker_convItoC(a) {
    return String.fromCharCode(a);
}
function spinnaker_convCtoI(a) {
    return a.charCodeAt();
}

let chrbuffer = ""
function spinnaker_putChr(c,rw) {
    chrbuffer = chrbuffer + c;
    if (c === '\n') {
        process.stdout.write(chrbuffer);
        chrbuffer = "";
    }
    return rw;
}

let fs = require("fs");
function spinnaker_getChr(rw) {
    process.stdout.write(chrbuffer);
    chrbuffer = "";
    let buffer = Buffer.alloc(4);
    fs.readSync(0,buffer,0,1,null);
    let fst = buffer[0];
    if (fst < 0xe0) {
        if(fst > 0x7F) {
            fs.readSync(0,buffer,1,1,null);
        }
    } else if (fst < 0xf0) {
        fs.readSync(0,buffer,1,2,null);
    } else {
        fs.readSync(0,buffer,1,3,null);
    }
    let string = buffer.toString('utf8');
    return new Tup2(string.substr(0,string.indexOf('\0')), rw);
}

//TODO spinnaker_putChr serio, spinnaker_getChr serio, spinnaker_isEOF
function spinnaker_exit(a) {
    process.exit(0);
    return a;
}
