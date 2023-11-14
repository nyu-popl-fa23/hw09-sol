const repeat = function(s: String) {
  return function loop(n: Num): String {
    return n === 0 ? "" : s + loop(n - 1)
  }
};

console.log('repeat("a")(3)');
console.log(repeat("a")(3));

console.log('repeat("xyz")(2)');
console.log(repeat("xyz")(2))
