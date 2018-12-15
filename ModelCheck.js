
const sigma = 2, // { 0, 1 }, but can be increased as needed
      fs = require('fs'),
      linkedlist = require('./LinkedList'),
      Transducers = require('./Transducers'),
      { PLUS, MINUS, EQ1, EQ } = Transducers,
      writeToFile = (T, name) => fs.writeFile(`./constructions/${name}`, JSON.stringify(T), 'utf8'),
      ithChar = (i, tracks) => Number(i).toString(sigma).padStart(tracks, '0'),
      charInd = char => parseInt(char, sigma),
      stateListFromSet = set => Object.keys(set).map(x => parseInt(x)).sort((a, b) => a - b),
      hashFromStateList = l => l.join(','),
      listFromHash = hash => hash.split(',').map(x => parseInt(x)),
      isFinal = (T, s) => T.accept ? T.final[s] : !T.final[s],
      labelsToTracks = (labels, table) => {
        var r = labels.map(l => table.indexOf(l));
        if (r.indexOf(-1) === -1)
            return r;
        else
            throw new Error('Track labels must agree');
      },
      pad = inputStrs => {
        var maxLen = inputStrs.map(x => x.length).reduce((a, b) => Math.max(a, b));
        return inputStrs.map(x => x.padEnd(maxLen, '0'));
      },
      reverse = str => {   
        for (var i = str.length - 1, rev = ''; i >= 0; i--)      
            rev += str[i]; 
        return rev;
      },
      copy = M => {
        var T = Object.assign({}, M);
        T.trackLabels = T.trackLabels.slice();
        return T;
      },
      reverseBinary = n => reverse(Number(n).toString(2)),
      getArrayBySC = (sc, len) => sc > 65536 ? new Uint32Array(len) : sc > 256 ?
        new Uint16Array(len) : new Uint8Array(len),
      getArrayBySize = (bpe, len) => bpe === 4 ? new Uint32Array(len) : bpe === 2 ?
        new Uint16Array(len) : new Uint8Array(len),
      SAT = T => typeof T === 'boolean' ? T : T.accept ? T.finalSize >
        0 : T.sc - T.finalSize > 0,
      AND = (T1, T2) => product(T1, T2, true),
      OR = (T1, T2) => product(T1, T2, false),
      NOT = T => negate(T, true),
      EXISTS = (boundedVars, P) => rabinScott(P, boundedVars),
      FORALL = (boundedVars, P) => NOT(EXISTS(boundedVars, NOT(P)));

function isTransducer(T) {
    // by erasing all tracks you have only a boolean
    if (typeof T === 'boolean')
        return true;

    // only supports 2^32 states
    // to get 2^64, will need two delta arrays, and T.sc to be a bigint
    // also the parseInt in rabinScott will need to be a BigInt
	if (T.sc <= 0 || T.sc >= Math.pow(2, 32) || T.delta.length !== T.sc)
		return false;

	if (T.tracks < 0)
		return false;

	var alphabet = Math.pow(sigma, T.tracks);

	if (T.delta.some(deltaS =>
		deltaS.length !== alphabet ||
          deltaS.some(nextState => nextState < 0 || nextState >= T.sc)
	))
		return false;

    if (typeof T.accept !== 'boolean' || T.finalSize !== Object.keys(T.final).length)
        return false;

	for (let s in Object.keys(T.final))
		if (s < 0 || s >= T.sc)
			return false;

    for (var i = 0; i < T.tracks; i++)
        if (!T.trackLabels[i])
            return false;

	return true;
}

// takes a deterministic transducer and tracks to erase, and returns the rabin
// scott transitive closure determinization
// O(2^n) (sort of, this assumes the number of characters is fixed)
function rabinScott(T, trackLabelsErased) {

    if (trackLabelsErased.length === T.tracks)
        return SAT(T);

    var states = { '0': 0 }, // map from hashes of sets of states of old machine to their label
        tracksErased = labelsToTracks(trackLabelsErased, T.trackLabels),
        tracksKept = getTracksKept(tracksErased.sort((a, b) => a - b), T.tracks),
        Tnew = {
            delta: [],
            final: {},
            tracks: tracksKept.length,
            trackLabels: tracksKept.map(t => T.trackLabels[t]),
            accept: true,
            finalSize: 0
        },
        erasedTo = smallToBigAlphabet(T.tracks, tracksKept),
        alphabetSize = Math.pow(sigma, Tnew.tracks),
        frontier = linkedlist.singleton({ h: '0', s: [0], l: 0 }), // linkedlist of new states hashes and lists (not yet in delta, but already discovered)
        newStateLabel = 1; // number of states we know about

    while (!frontier.e) { // while linkedlist isn't empty

        var lookup = linkedlist.deq(frontier),
            hash = lookup.h, // the unique string representing this state
            state = lookup.s, // state is current state (list of state labels from T)
            label = lookup.l, // label is its label in Tnew
            deltaS = getArrayBySC(newStateLabel + alphabetSize, alphabetSize); // need array that can handle 2^T.sc states, of length alphabetSize

        // for each character in our new alphabet
        for (var i = 0; i < alphabetSize; i++) {
            var charIPreimage = erasedTo[i],
                nextStateSet = {};

            for (var j = 0; j < charIPreimage.length; j++)
                for (var k = 0, oldCharInd = charIPreimage[j]; k < state.length; k++)
                    nextStateSet[T.delta[state[k]][oldCharInd]] = true;

            var nextStateList = stateListFromSet(nextStateSet),
                nextStateHash = hashFromStateList(nextStateList);

            // if set we transition to was already seen, map to the label of that state
            lookup = states[nextStateHash];
            if (lookup !== undefined)
                deltaS[i] = lookup;
            else { // otherwise give this new set the next label
                deltaS[i] = newStateLabel;
                states[nextStateHash] = newStateLabel;
                linkedlist.enq(frontier, { h: nextStateHash, s: nextStateList, l: newStateLabel });
                newStateLabel++;
            }
        }

        // if it contains a state which was final, this set of states is final
        if (state.some(T.accept ? st => T.final[st] : st => !T.final[st])) {
            Tnew.final[label] = true;
            Tnew.finalSize++;
        }
        // with linkedlist you go in order, not with stack
        Tnew.delta.push(deltaS);
    }

    Tnew.sc = newStateLabel;
    return Tnew;
}

// takes transitive closure product O(n^2)
// O(n^2) (sort of, this assumes the number of characters is fixed)
function product(T1, T2, both) {

    var states = { '0,0': 0 }, // map from hashes of pairs of states of old machines to their new label
        F = T1.tracks > T2.tracks ? T2 : T1, // F is the machine with fewer tracks
        M = T1.tracks > T2.tracks ? T1 : T2; // M is the machine with more tracks

    // if the bigger machine doesn't have a track for every variable in the smaller,
    // reindex its characters to include an ignored track
    if (!F.trackLabels.every(x => M.trackLabels.includes(x)))
        M = addIgnoredTracks(M, F.trackLabels, true);

    var alphabetSize = Math.pow(sigma, M.tracks),
        Tnew = {
            delta: [],
            final: {},
            tracks: M.tracks,
            trackLabels: M.trackLabels.slice(),
            accept: true,
            finalSize: 0
        },
        bigToSmallAlph = bigToSmallAlphabet(M, F, alphabetSize), // maps charInd of bigger alphabet to set of corresponding smaller charInds
        frontier = linkedlist.singleton({ h: '0,0', m: 0, f: 0, l: 0 }), // linkedlist of new state hashes and lists (not yet in delta, but already in states)
        newStateLabel = 1; // number of states we know about

    while (!frontier.e) {

        var lookup = linkedlist.deq(frontier),
            hash = lookup.h, // the unique string representing this state
            stateM = lookup.m, // current state pair
            stateF = lookup.f,
            label = states[hash], // label is its label in Tnew
            deltaS = getArrayBySC(newStateLabel + alphabetSize, alphabetSize);

        // for each character in our new alphabet
        for (var i = 0; i < alphabetSize; i++) {

            var charIndF = bigToSmallAlph[i],
                nextStateM = M.delta[stateM][i],
                nextStateF = F.delta[stateF][charIndF],
                nextStateHash = nextStateM + ',' + nextStateF;

            // if set we transition to was already seen, map to its index
            lookup = states[nextStateHash];
            if (lookup !== undefined)
                deltaS[i] = lookup;
            else { // otherwise give this new set the next index
                deltaS[i] = newStateLabel;
                states[nextStateHash] = newStateLabel;
                linkedlist.enq(frontier, { h: nextStateHash, m: nextStateM, f: nextStateF });
                newStateLabel++;
            }
        }

        // determine if state is final (and vs or)
        if (both ? isFinal(M, stateM) && isFinal(F, stateF) : isFinal(M, stateM) || isFinal(F, stateF)) {
            Tnew.final[label] = true;
            Tnew.finalSize++;
        }

        Tnew.delta.push(deltaS);
    }

    Tnew.sc = newStateLabel;
    return Tnew;
}

// helper for erasing tracks in rabin-scott
// maps each character index of new machine to set of indices that erased to it
function smallToBigAlphabet(oldTrackCount, tracksKept) {
    // initialize map
    for (var i = 0, res = []; i < Math.pow(sigma, tracksKept.length); i++)
        res.push([]);

    // for each old character, add it to the row of the char it erases to
    for (var i = 0; i < Math.pow(sigma, oldTrackCount); i++) {
        var charOld = ithChar(i, oldTrackCount),
            charNew = '';
        
        for (var j = 0; j < tracksKept.length; j++)
            charNew += charOld[tracksKept[j]];

        res[charInd(charNew)].push(i);
    }

    return res;
}

// helper for rabin-scott, returns indices of tracks not erased
function getTracksKept(tracksErased, oldTrackCount) {

    for (var i = 0, pos = 0, kept = []; i < oldTrackCount; i++) {
        if (pos >= tracksErased.length || i < tracksErased[pos])
            kept.push(i);
        if (pos < tracksErased.length && i >= tracksErased[pos])
            pos++;
    }

    return kept;
}

// helper for erasing tracks in the product
// maps each character index of new machine to set of indices that erased to it
function bigToSmallAlphabet(moreTracks, fewerTracks, alphabetSize) {

    var tracksUsed = [],
        bigToSmall = [];

    for (var i = 0; i < fewerTracks.tracks; i++) {
        var ind = moreTracks.trackLabels.indexOf(fewerTracks.trackLabels[i]);
        if (ind === -1)
            throw new Error('Track labels must agree');

        tracksUsed.push(ind);
    }

    for (var i = 0; i < alphabetSize; i++) {

        var charMore = ithChar(i, moreTracks.tracks),
            charFewer = '';

        for (var j = 0; j < tracksUsed.length; j++)
            charFewer += charMore[tracksUsed[j]];

        bigToSmall.push(charInd(charFewer)); // index i maps char i in the big alphabet to what it erases to
    }

    return bigToSmall;
}

// flip the accept and reject states, and optionally make a shallow copy of the
// machine as to not negate the original
function negate(T, doCopy) {
    if (doCopy)
        T = copy(T);

    T.final = !T.final;
    return T;
}

// run a transducer on its input (input is an array of strings, one per track)
function run(x, T) {
    // if we have a 0 track machine, the output is constant
    if (typeof T === 'boolean')
        return T;

    if (!x.length === T.tracks)
        throw new Error('Wrong number of inputs');

    x = pad(x);

    for (var i = 0, state = 0; i < x[0].length; i++) {
        var char = '';

        for (var j = 0; j < T.tracks; j++)
            char += x[j][i];

        state = T.delta[state][charInd(char)];
    }

    // !! to cast to boolean if undefined
    return T.accept ? !!T.final[state] : !T.final[state];
}

// note this method modifies T, doesn't create a copy
// add a new track to T for each label in newLabel (must reindex the characters)
function addIgnoredTracks(T, newLabels, doCopy) {

    if (doCopy)
        T = copy(T);

    newLabels = newLabels.filter(x => !T.trackLabels.includes(x));

    var res = copy(T),
        num = newLabels.length,
        alphabetSize = Math.pow(sigma, T.tracks + num);

    res.tracks = T.tracks + num;
    res.delta = [];
    res.trackLabels.push(...newLabels);

    for (var i = 0; i < T.sc; i++) {
        var oldStateTable = T.delta[i],
            newStateTable = getArrayBySize(oldStateTable.BYTES_PER_ELEMENT, alphabetSize);

        for (var j = 0; j < alphabetSize; j++)
            // the ith char is just i in binary, so right shifting ignores the last num many tracks
            newStateTable[j] = oldStateTable[j >> num];

        res.delta.push(newStateTable);
    }

    return res;
}

// constructs the machine that accepts (<x>, <y>) iff x * y = k (stringing additions)
// this allows for nondeterminism, question of whether or not construct a k track
// machine, and then determinize, or to determinze each time an addition is carried out
function timesConstant(k, inputLabel, outputLabel, determinizeEachStep) {
   var M = copy(PLUS),
       A = copy(EQ),
       charCode = 65,
       prev,
       exists,
       reserved = [inputLabel.charCodeAt(0), outputLabel.charCodeAt(0)],
       nextLabel = () => { // need unused track labels
           var l = String.fromCharCode(charCode);
           charCode++;
           return reserved.includes(l) ? nextLabel() : (reserved.push(l) || true) && l;
       };

    M.trackLabels[0] = A.trackLabels[0] = inputLabel;
    M.trackLabels[1] = A.trackLabels[1] = exists = nextLabel();
    M.trackLabels[2] = prev = k === 2 ? outputLabel : nextLabel();

    M = AND(M, A);

    if (determinizeEachStep)
        M = rabinScott(M, [exists])

    for (var i = 0; i < k - 2; i++) {
        var T = copy(PLUS);

        T.trackLabels[0] = inputLabel;
        T.trackLabels[1] = exists = prev;
        T.trackLabels[2] = prev = i === k - 3 ? outputLabel : nextLabel();

        M = addIgnoredTracks(M, [prev], false);
        M = AND(M, T);

        if (determinizeEachStep)
            M = rabinScott(M, [exists]);
    }

    if (determinizeEachStep)
        return M;

    // everything track except the input label and output label will be erased
    reserved.shift();
    reserved.shift();

    return rabinScott(M, reserved);
}


// construct the machine that accepts (<x>, <y>) <=> Ax - By = 1
function linearDiophantine(A, B, determinize) {
    
    var minus = copy(MINUS),
        eq1 = copy(EQ1),
        timesA = timesConstant(A, 'x', 'Ax', true),
        timesB = timesConstant(B, 'y', 'By', true);

    minus.trackLabels = ['Ax', 'By', 'z']; // Ax - By = z
    eq1.trackLabels = ['z']; // z = 1

    var t = determinize ? rabinScott(AND(minus, eq1), ['z']) : AND(minus, eq1),
        t1 = determinize ? rabinScott(AND(t, timesA), ['Ax']) : AND(t, timesA);

    return rabinScott(AND(t1, timesB), determinize ? ['By'] : ['Ax', 'By', 'z']);
}

// assuming M acts on reverse binary strings, test its output against the output
// of the lambda with all combinations of all strings up to length inputLength
// (assertion will be passed the numerical value of the strings M is passed)
function testArithmetic(M, assertion, inputLen) {
    if (sigma !== 2)
        throw new Error('Arithmetic test requires reverse binary encoding (sigma = 2)');

    var numTests = Math.pow(sigma, inputLen * M.tracks),
        mask = Math.pow(sigma, inputLen) - 1;

    for (var i = 0; i < numTests; i++) {
        var inputStrs = [],
            inputVals = [];

        for (var j = 0; j < M.tracks; j++) {
            var val = (i >> (inputLen * j)) & mask;
            inputVals.push(val);
            inputStrs.push(reverseBinary(val));
        }

        inputStrs = pad(inputStrs);

        var resActual = run(inputStrs, M),
            resExpected = assertion(...inputVals);

        if (resActual !== resExpected) {
            console.log(`\nTest Failed On Input: <${inputVals}> (encoded as <${inputStrs}>)` + 
                `\n\nExpected ${resExpected}, got ${resActual}\n`);
            return false;
        }
    }

    return true;
}

module.exports = { AND, OR, EXISTS, FORALL, SAT, NOT, timesConstant, linearDiophantine, run,
    testArithmetic, copy, reverseBinary, writeToFile, addIgnoredTracks, isTransducer, Transducers };
