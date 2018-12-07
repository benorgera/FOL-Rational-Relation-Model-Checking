
const sigma = 2, //0, 1, #
      ithChar = (i, tracks) => Number(i).toString(sigma).padStart(tracks, '0'),
      charInd = char => parseInt(char, sigma),
      uniqueHash = set => Object.keys(set).sort((a, b) => a - b).join(','),
      listFromHash = hash => hash.split(',').map(x => parseInt(x)),
      isFinal = (T, s) => T.accept ? T.final[s] : !T.final[s],
      labelsToTracks = (labels, table) => {
        var r = labels.map(l => table.indexOf(l));
        if (r.indexOf(-1) === -1)
            return r;
        else
            throw new Error('Track labels must agree');
      },
      getArray = () => [],
      // getArray = oldSc => oldSc > 32 ? new BigUint64Array() : oldSc > 16 ?
      //   new Uint32Array() : oldSc > 8 ? new Uint16Array() : new Uint8Array();
      isSatisfiable = T => typeof T === 'boolean' ? T : T.accept ? T.finalSize >
        0 : T.sc - T.finalSize > 0,
      AND = (T1, T2) => product(T1, T2, true),
      OR = (T1, T2) => product(T1, T2, true),
      NOT = T => negate(T),
      EXISTS = (boundedVars, P) => rabinScott(P, boundedVars),
      FORALL = (boundedVars, P) => NOT(EXISTS(boundedVars, NOT(P)));

var binaryAdd = {
    delta: [[0,2,2,0,2,0,1,2],[2,0,1,2,1,2,2,1],[2,2,2,2,2,2,2,2]],
    sc: 3,
    tracks: 3,
    trackLabels: ['x', 'y', 'z'],
    final: { 0: true },
    accept: true, // if final F or Q \ F
    finalSize: 1
}

function isTransducer(T) {
    // by erasing all tracks you have only a boolean
    if (typeof T === 'boolean')
        return true;

    // to get 2^64, will need two delta arrays, and T.sc to be a bigint
    // also the parseInt in rabinScott will need to be a BigInt
	if (T.sc <= 0 || T.sc >= Math.pow(2, 32) || T.delta.length !== T.sc)
		return false;

	if (T.tracks < 0)
		return false;

	var alphabet = Math.pow(sigma, T.tracks);

	if (T.delta.some(deltaS =>
		deltaS.length !== alphabet || Math.pow(2, 8 * deltaS.BYTES_PER_ELEMENT)
          < T.sc || deltaS.some(nextState => nextState < 0 || nextState >= T.sc)
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

// map from new alphabet to the characters in the old alphabet which erase to it
function newCharsToOldChars(oldTrackCount, tracksKept) {
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

function getTracksKept(tracksErased, oldTrackCount) {

    for (var i = 0, pos = 0, kept = []; i < oldTrackCount; i++) {
        if (pos >= tracksErased.length || i < tracksErased[pos])
            kept.push(i);
        if (pos < tracksErased.length && i >= tracksErased[pos])
            pos++;
    }

    return kept;
}

function rabinScott(T, trackLabelsErased) {

    if (trackLabelsErased.length === T.tracks)
        return isSatisfiable(T);

    var states = { '0': 0 }, // map from hashes of sets of states of old machine to their label
        tracksErased = labelsToTracks(trackLabelsErased, T.trackLabels),
        tracksKept = getTracksKept(tracksErased.sort((a, b) => a - b), T.tracks),
        Tnew = {
            delta: [],
            final: {},
            tracks: T.tracks - tracksErased.length,
            sc: 0, // number of reachable sets of states added to delta so far
            trackLabels: tracksKept.map(t => T.trackLabels[t]),
            accept: true,
            finalSize: 0
        },
        erasedTo = newCharsToOldChars(T.tracks, tracksKept),
        newAlphabetSize = Math.pow(sigma, Tnew.tracks),
        frontier = ['0']; //queue of new state sets (not yet in delta, but already in states)
        // so frontier[Tnew.sc] is next state needing attention

    while (frontier.length > Tnew.sc) {

        var stateSetHash = frontier[Tnew.sc],
            stateSet = listFromHash(stateSetHash),
            deltaS = getArray(T.sc); // need array that can handle 2^T.sc states

        // console.log('\nCurrent State Set: ' + stateSetHash);

        // for each character in our new alphabet
        for (var i = 0; i < newAlphabetSize; i++) {

            var charIPreimage = erasedTo[i],
                nextStateSet = {};

            for (var j = 0; j < charIPreimage.length; j++)
                for (var k = 0, oldCharInd = charIPreimage[j]; k < stateSet.length; k++)
                    nextStateSet[T.delta[stateSet[k]][oldCharInd]] = true;

            var nextStateSetHash = uniqueHash(nextStateSet);
            // console.log(`-char ${i} goes to: `, nextStateSetHash);

            // if set we transition to was already seen, map to its index
            if (states[nextStateSetHash] !== undefined)
                deltaS.push(states[nextStateSetHash]);
            else { // otherwise give this new set the next index
                deltaS.push(frontier.length);
                states[nextStateSetHash] = frontier.length;
                frontier.push(nextStateSetHash);
            }
        }

        // if it contains a state which was final, this set of states is final
        if (stateSet.some(T.accept ? s => T.final[s] : s => !T.final[s])) {
            Tnew.final[Tnew.sc] = true;
            Tnew.finalSize++;
        }

        Tnew.delta.push(deltaS);
        Tnew.sc++;
    }

    return Tnew;
}

// O(1), just annoying
function bigToSmallAlphabet(moreTracks, fewerTracks, alphabetSize) {

    var tracksUsed = [],
        bigToSmall = [];

    for (var i = 0; i < fewerTracks.tracks; i++) {
        var ind = moreTracks.trackLabels.indexOf(fewerTracks.trackLabels[i]);
        if (ind === -1)
            throw new Error('Track labels must agree');

        tracksUsed.push(ind);
    }

    tracksUsed.sort((a, b) => a - b);

    for (var i = 0; i < alphabetSize; i++) {

        var charMore = ithChar(i, moreTracks.tracks),
            charFewer = '';

        for (var j = 0; j < tracksUsed.length; j++)
            charFewer += charMore[tracksUsed[j]];

        bigToSmall.push(charInd(charFewer)); // index i maps char i in the big alphabet to what it erases to
    }

    return bigToSmall;
}

function product(T1, T2, both) {
     var states = { '0,0': 0 }, // map from hashes of pairs of states of old machines to their new label
        F = T1.tracks > T2.tracks ? T2 : T1, // F is the machine with fewer tracks
        M = T1.tracks > T2.tracks ? T1 : T2, // M is the machine with more tracks
        alphabetSize = Math.pow(sigma, M.tracks),
        Tnew = {
            delta: [],
            final: {},
            tracks: M.tracks,
            sc: 0, // number of reachable sets of states added to delta so far
            trackLabels: M.trackLabels.slice(),
            accept: true,
            finalSize: 0
        },
        bigToSmallAlph = bigToSmallAlphabet(M, F, alphabetSize), // maps charInd of bigger alphabet to set of corresponding smaller charInds
        frontier = ['0,0']; // queue of new state sets (not yet in delta, but already in states)
        // so frontier[Tnew.sc] is next state needing attention

    while (frontier.length > Tnew.sc) {

        var stateSetHash = frontier[Tnew.sc],
            [ stateM, stateF ] = listFromHash(stateSetHash),
            deltaS = getArray(Tnew.sc); // need array that can handle 2^T.sc states

        // console.log('\nCurrent State Pair: ' + stateSetHash);

        // for each character in our new alphabet
        for (var i = 0; i < alphabetSize; i++) {

            var charIndF = bigToSmallAlph[i],
                nextStateM = M.delta[stateM][i],
                nextStateF = F.delta[stateF][charIndF],
                nextStateHash = nextStateM + ',' + nextStateF;

            // console.log(`-char ${i} goes to: `, nextStateHash);

            // if set we transition to was already seen, map to its index
            if (states[nextStateHash] !== undefined)
                deltaS.push(states[nextStateHash]);
            else { // otherwise give this new set the next index
                deltaS.push(frontier.length);
                states[nextStateHash] = frontier.length;
                frontier.push(nextStateHash);
            }
        }

        // determine if state is final (and vs or)
        if (both ? isFinal(M, stateM) && isFinal(F, stateF) : isFinal(M, stateM) || isFinal(F, stateF)) {
            Tnew.final[Tnew.sc] = true;
            Tnew.finalSize++;
        }

        Tnew.delta.push(deltaS);
        Tnew.sc++;
    }

    return Tnew;
}

// flip the accept and reject states, and optionally make a shallow copy of the
// machine as to not negate the original
function negate(T, copy) {
    if (copy) {
        var res = Object.assign({}, T);
        res.final = !res.final;
        return res;
    } else {
        T.final = !T.final;
        return T;
    }
}

console.log(binaryAdd)
console.log(isTransducer(binaryAdd))

var res = rabinScott(binaryAdd, ['z']);
 console.log(isTransducer(res));
 var res3 = FORALL(['x'], AND(binaryAdd, res));
 console.log(isTransducer(res3));
 console.log(res3);
 console.log(binaryAdd);
var res2 = AND(OR(res3, binaryAdd), res);
console.log(isTransducer(res2));
console.log(res2);
// res1 = EXISTS(['y'], res2);
// console.log(isTransducer(res1));
// console.log(res1);
