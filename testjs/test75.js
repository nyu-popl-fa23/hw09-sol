const f = function f(x: Num): Num { return x === 0 ? 1 : x * f(x - 1) };
f(8) + 0.1
