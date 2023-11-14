const g = function f(x: Num): Num { return x === 0 ? 1 : x * f(x - 1) };
(function(x: Num) {
  const f = g;
  return f(x) + 0.1
})(8)
