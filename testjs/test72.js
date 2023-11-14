const g = function(x: Num, y: Num) { return x && y /* type error */};
g(1)(0) + 0.1
