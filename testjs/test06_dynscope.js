const x = 1;
const r = (function(x: Num) { return 2; })(3) + x;
console.log(r);

const x = 1;
const g = function(y: Num) { return x; };
const h = function(x: Num) { return g(2); };
console.log(h(3));

const x = 42;
const plus = function(x: Num, y: Num) { return x + y; };
console.log(plus(3, 4));
