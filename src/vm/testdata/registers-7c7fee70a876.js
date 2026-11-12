class se {
constructor() {
var GS_0_1;
this.H = P8(new qt(256), 0);
this.J = P8(new qt(256), 0);
GS_0_1 = this.O = IS_55() * 4294967296 | 0;
this.h = (GS_0_1 ^ GS_0_1 >>> 29) << 3 >> 3;
this.F = this.D = -1;
this.m = this.j = 1;
this.l = this.i = 0;
this.v = this.A = undefined;
}
get ["O"]() {
return this.L | this.K << 16;
}
set ["O"](GS) {
this.L = GS & 65535;
this.K = GS >>> 16;
}
}
function IQ(GS, Go) {
var Gw, Gu;
Gw = GS.J[Go];
Gu = Gw & 3;
if (Gu === 1) {
return GS.H[Go] ^ Gw >> 2;
} else {
if (Gu === 2) {
return 0 !== (GS.H[Go] ^ Gw >> 2);
} else {
if (3 === Gu) {
if (GS.D === Go) {
if (GS.j === 1) {
return GS.h ^ GS.i;
} else {
return GS.A;
}
} else {
if (GS.m === 1) {
return GS.l ^ GS.h;
} else {
return GS.v;
}
}
} else {
if (-4 === Gw) {
return Ty(GS.H[Go]);
} else {
return GS.H[Go];
}
}
}
}
}
function In(GQ, GS) {
if (typeof GS === "number" && (0 | GS) === GS && (GS !== 0 || 1 / GS > 0)) {
GQ.j = 1;
GQ.i = GS ^ GQ.h;
} else {
GQ.j = 0;
GQ.A = GS;
}
}
function Ig(GQ, GS) {
if (typeof GS === "number" && GS === (GS | 0) && (0 !== GS || 1 / GS > 0)) {
GQ.m = 1;
GQ.l = GQ.h ^ GS;
} else {
GQ.m = 0;
GQ.v = GS;
}
}
function Iw(GQ, Go, GS) {
if (Go === GQ.D) In(GQ, GS);
else if (GQ.F === Go) Ig(GQ, GS);
else if ("number" === typeof GS) {
let Gw = 0 | GS;
if (GS === Gw && (0 !== GS || 1 / GS > 0)) {
qT(GQ, Go, Gw, 1);
} else {
q1(GQ, Go, GS, 4607060 ^ Gw);
}
} else if (typeof GS === "boolean") {
qT(GQ, Go, GS ? 1 : 0, 2);
} else {
q1(GQ, Go, GS, typeof GS === "string" ? 5461074 ^ GS.length : undefined === GS ? 5590596 : GS === null ? 5133644 : 5194314);
}
}
function kib_1(Yhb, Zhb, aib) {
if (Yhb.D === Zhb) {
In(Yhb, aib);
} else {
if (Yhb.F === Zhb) {
Ig(Yhb, aib);
} else {
q1(Yhb, Zhb, aib, 5194314);
}
}
return;
}
