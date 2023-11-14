const byvalue = function(const x: Num) { return x + x };

const byname = function(name x: Num) { return x + x };

const byvar = function(let x: Num) { x = x + 1; return x };

const byref = function(ref x: Num) { x = x + 1; return x };

let y = 3;

const vy = byvalue(y + 1);
console.log(y);
console.log(vy);

y = 3;

const ny = byname(y + 1);
console.log(y);
console.log(ny);

y = 3;

const vry = byvar(y);
console.log(y);
console.log(vry);

y = 3;

const ry = byvar(y);
console.log(y);
console.log(ry);

let x = 1;
const f = function(name x: Num, y: Num) { return x + x + y; };
f(x = x + 1, 1)