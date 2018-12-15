
// load module and extract needed objects into our scope
var MC = require('./ModelCheck'),
  { PLUS, EQ, LT, MINUS, EQ1 } = MC.Transducers,
  { AND, OR, EXISTS, FORALL, SAT, timesConstant, linearDiophantine,
  	run, testArithmetic, isTransducer, addIgnoredTracks, copy } = MC;

var EQANDPLUS = AND(EQ, PLUS), // x + y = z and x = y
    EQORPLUS = OR(EQ, PLUS),
    LTANDPLUS = AND(LT, PLUS),
    LTORPLUS = OR(LT, PLUS),
    LTANDPLUSOREQ = OR(LTANDPLUS, EQ); 

// useful for debugging
console.log('Data Structure Invariant: ' + (isTransducer(EQANDPLUS) && isTransducer(EQORPLUS) 
	&& isTransducer(EXISTS(['x'], LTANDPLUSOREQ))
	 && isTransducer(FORALL(['y'], EQANDPLUS))));

// simple tests
console.log('6 + 6 = 12 and 6 = 6: ' + run(['0110', '0110', '0011'], EQANDPLUS));
console.log('4 + 6 = 10 and 4 = 6: ' + run(['001', '011', '0101'], EQANDPLUS));

// more general tests (tests all combinations of strings on tracks up to the string <2^6 - 1>)
// (note that this is 64^tracks many tests)
console.log('+ transducer matches + function up to 2^6 (correctness assertion): ' + testArithmetic(PLUS, (x, y, z) => x + y === z, 6));
console.log('Example failed correctness assertion (plus transducer matches minus function): ');
testArithmetic(PLUS, (x, y, z) => x - y === z, 6);
console.log('Correctness of x = y and x + y = z up to 2^6: ' + testArithmetic(EQANDPLUS,
	(x, y, z) => x === y && x + y === z, 6));
console.log('Correctness of - up to 2^6: ' + testArithmetic(MINUS, (x, y, z) => x - y === z));
console.log('Correctness of (x < y and x + y = z) or x = y to 2^6: ' + testArithmetic(LTANDPLUSOREQ,
	(x, y, z) => (x < y && x + y === z) || x === y, 6));

// some multiplication tests (flag decides if you erase tracks as you go, 
// experimentally seems to compute bigger machines faster)
var T3 = timesConstant(3, 'x', 'y', false),
    T6 = timesConstant(6, 'x', 'y', false),
    T10 = timesConstant(10, 'x', 'y', true);

// leading zeros are not needed by run
console.log('3 x 3 = 9: ' + run(['11', '1001'], T3));
console.log('6 x 2 = 12: ' + run(['01', '0011'], T6));
console.log('6 x 18 = 108: ' + run(['01001', '0011011'], T6));
console.log('10 x 7 = 70: ' + run(['111', '0110001'], T10));
console.log('3 x 4 = 11: ' + run(['001', '1101'], T3));
console.log('6 x 9 = 64: ' + run(['1001', '0000001'], T6));
console.log('10 x 9 = 70: ' + run(['1001', '0110001'], T10));
console.log('10 x 7000 = 70000: ' + run(['0001101011011', '00001110100010001'], T10));


console.log('Correctness of 3x = y up to 2^6: ' + testArithmetic(T3, (x,y) => 3 * x === y, 6));
console.log('Correctness of 6x = y up to 2^6: ' + testArithmetic(T6, (x,y) => 6 * x === y, 6));
console.log('Correctness of 10x = y up to 2^6: ' + testArithmetic(T10, (x,y) => 10 * x === y, 6));

// example of adding ignored tracks
var A = addIgnoredTracks(PLUS, ['a', 'b'], true);
console.log('2 + 1 = 3 With Ignored Tracks: ' + run(['01', '10', '11', '01', '00'], A));


// solving linear diophantines
var L = linearDiophantine(6, 5, true);
console.log('Exists x, y st. 6x - 5y = 1: ' + EXISTS(['x', 'y'], L));

// also note that we maintain a reachability invariant so asking about satisfiability
// of a machine (exists or for all statements which bind all variables/erase all tracks)
// takes constant work by taking the size of set of final states

var L2 = linearDiophantine(9, 6, true); // this one takes 16 seconds to compute
console.log('Exists x, y st. 9x - 6y = 1: ' + SAT(L2));

// probably not minimal, will be implementing hopcrofts at some point to see just how bad they actually are
console.log('How many states did 6x - 5y = 1 take: ' + L.sc);
console.log('How many states did 9x - 6y = 1 take: ' + L2.sc);


// note that exists/forall can be used to just remove some tracks and make machine a function of
// smaller alphabet, ie.
var DIV3 = EXISTS(['x'], T3);
console.log('3 | 9: ' + run(['1001'], DIV3));
console.log('7 | 9: ' + run(['111'], DIV3));

console.log('Correctness of 3 | x up to 2^6: ' + testArithmetic(DIV3, (x,y) => x % 3 === 0, 6));

console.log('5x - 6y = 1 is satisfiable: ' + SAT(L));
console.log('9x - 6y = 1 is satisfiable: ' + SAT(L2));
