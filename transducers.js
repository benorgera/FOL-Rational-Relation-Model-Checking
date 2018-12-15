// all of these machines take in reverse binary encoded numbers
// the padding character is 0 (ie. the number one can be any of 1, 10, 100, ...)


// accepts (<x>, <y>, <z>) iff x + y = z
var PLUS = {
    delta: [[0,2,2,0,2,0,1,2],[2,0,1,2,1,2,2,1],[2,2,2,2,2,2,2,2]],
    sc: 3,
    tracks: 3,
    trackLabels: ['x', 'y', 'z'],
    final: { 0: true },
    accept: true, // if final is F or Q \ F
    finalSize: 1
}

// accepts (<x>, <y>) iff x = y
var EQ = {
    delta: [[0,1,1,0], [1,1,1,1]],
    sc: 2,
    tracks: 2,
    trackLabels: ['x', 'y'],
    final: { 0: true },
    accept: true, // if final is F or Q \ F
    finalSize: 1
}

// accepts <x> iff x = 1
var EQ1 = {
    delta: [[2,1],[1,2],[2,2]],
    sc: 3,
    tracks: 1,
    trackLabels: ['x'],
    final: { 1: true },
    accept: true, // if final is F or Q \ F
    finalSize: 1
}

// accepts (<x>, <y>) iff x < y
var LT = {
    delta: [[0,1,0,0],[1,1,0,1]],
    sc: 2,
    tracks: 2,
    trackLabels: ['x', 'y'],
    final: { 1: true },
    accept: true, // if final is F or Q \ F
    finalSize: 1
}

// accepts (<x>, <y>, <z>) iff x - y = z, where - is proper subtraction
var MINUS = {
    delta: [[0,2,2,1,2,0,0,2],[2,1,1,2,0,2,2,1],[2,2,2,2,2,2,2,2]],
    sc: 3,
    tracks: 3,
    trackLabels: ['x', 'y', 'z'],
    final: { 0: true },
    accept: true, // if final is F or Q \ F
    finalSize: 1
}

module.exports = { PLUS, EQ, LT, MINUS, EQ1 };
