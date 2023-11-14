const plus = function (x: Num, y: Num) { return x + y };

console.log( plus(3, 4) );


const for =
  function (f: (Num, Num) => Num) {
    return function reduce(n: Num, acc: Num): Num {
      return n === 0 ? acc : reduce(n - 1, f(n, acc))
    }
  };

const factorial =
  function (n: Num) {
    return for(function (i: Num, acc: Num) {
      return i * acc
    })(n, 1)
  };

console.log( factorial(4) );
console.log( factorial(5) );
