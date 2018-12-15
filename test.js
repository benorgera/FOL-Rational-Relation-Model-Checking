
// load module and extract needed objects into our scope
var MC = require('./ModelCheck.js'),
  { PLUS, EQ, LT, MINUS, EQ1 } = MC.Transducers,
  { AND, OR, EXISTS, FORALL, SAT, timesConstant, linearDiophantine,
  	run, testArithmetic, isTransducer, addIgnoredTracks, copy } = MC;

var EQANDPLUS = AND(EQ, PLUS), // x + y = z and x = y
    EQORPLUS = OR(EQ, PLUS),
    LTANDPLUS = AND(LT, PLUS),
    LTORPLUS = OR(LT, PLUS),
    LTANDPLUSOREQ = OR(LTANDPLUS, EQ); 


console.log('Data Structure Invariant: ' + isTransducer(EQANDPLUS));

// simple tests
console.log('6 + 6 = 12 and 6 = 6: ' + run(['0110', '0110', '0011'], EQANDPLUS));
console.log('4 + 6 = 10 and 4 = 6: ' + run(['001', '011', '0101'], EQANDPLUS));

// more general tests (tests all pairs of strings on tracks up to the string <2^6 - 1>)
console.log('+ transducer matches + function up to 2^6 (correctness assertion): ' + testArithmetic(PLUS, (x, y, z) => x + y === z, 6));
console.log('Example failed correctness assertion (plus transducer matches minus function): ');
testArithmetic(PLUS, (x, y, z) => x - y === z, 6);
console.log('Correctness of EQANDPLUS up to 2^6: ' + testArithmetic(EQANDPLUS, (x, y, z) => x === y && x + y === z, 6));
console.log('Correctness of - up to 2^6: ' + testArithmetic(MINUS, (x, y, z) => x - y === z, 6))

// some multiplication tests
var T3 = timesConstant(3, 'x', 'y'),
    T6 = timesConstant(6, 'x', 'y'),
    T10 = timesConstant(10, 'x', 'y', true);

// leading zeros are optional
console.log('3 x 3 = 9: ' + run(['11', '1001'], T3));
console.log('6 x 2 = 12: ' + run(['01', '0011'], T6));
console.log('6 x 18 = 118: ' + run(['01001', '110001'], T6));
console.log('10 x 7 = 70: ' + run(['111', '0110001'], T10));
console.log('3 x 4 = 11: ' + run(['001', '1101'], T3));
console.log('6 x 9 = 64: ' + run(['1001', '0000001'], T6));
console.log('10 x 9 = 70: ' + run(['1001', '0110001'], T10));
console.log('10 x 7000 = 70: ' + run(['0001101011011', '1101101011000'], T10));


console.log('Correctness of 6x = y up to 2^6: ' + testArithmetic(T6, (x,y) => 6 * x === y, 6));

// example of adding ignored tracks
var A = addIgnoredTracks(PLUS, ['a', 'b'], true);
console.log('Ignored Tracks 2 + 1 = 3: ' + run(['01', '10', '11', '01', '00'], A));


// example of linear diophantine
var L = linearDiophantine(6, 5, false);
console.log('6(1) - 5(1) = 1: ' + run(['1', '1'], L));
console.log(L)
console.log('Correctness of diophantine machine: ' + testArithmetic(L, (x, y) => 6 * x - 5 * y === 1, 6));

console.log('hereeeee')
// var L2 = linearDiophantine(14, 7, true); // unsatisfiable linear diophantine

// some exists examples
console.log('Exists x, y st. 5x - 6y = 1: ' + EXISTS(['x, y'], L));
console.log('Exists x, y st. 14x - 7y = 1: ' + EXISTS(['x, y'], L2));


// note that exists/forall can be used to just remove some tracks and make machine a function of
// smaller alphabet, ie.
var DIV3 = EXISTS(['x'], T3);
console.log('3 | 9: ' + run(['1001', DIV3]));

// also note that we maintain a reachability invariant so asking about satisfiability
// of a machine or its negation can be done in constant time by checking size of set of final states
console.log('5x - 6y = 1 is satisfiable: ' + SAT(L));
console.log('14x - 7y = 1 is satisfiable: ' + SAT(L2));
