
const sigma = 2, //0, 1, #
      ithChar = (i, tracks) => Number(i).toString(sigma).padStart(tracks, '0'),
      charInd = char => parseInt(char, sigma),
      uniqueHash = set => Object.keys(set).sort((a, b) => a - b).join(','),
      listFromHash = hash => hash.split(',').map(x => parseInt(x)),
      getArray = () => [];
      // getArray = oldSc => oldSc > 32 ? new BigUint64Array() : oldSc > 16 ?
      //   new Uint32Array() : oldSc > 8 ? new Uint16Array() : new Uint8Array();

var binaryAdd = {
    delta: [[0,2,2,0,2,0,1,2],[2,0,1,2,1,2,2,1],[2,2,2,2,2,2,2,2]],
    sc: 3,
    tracks: 3,
    finalStates: { 0: true, 1: true }
}

function isTransducer(T) {
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

	for (let s in Object.keys(T.finalStates))
		if (s < 0 || s >= T.sc)
			return false;

	return true;
}

// map from new alphabet to the characters in the old alphabet which erase to it
function newCharsToOldChars(newTrackCount, trackErased) {
    var res = [];

    for (var i = 0; i < Math.pow(sigma, newTrackCount); i++) {
        res.push([]);
        var char = ithChar(i, newTrackCount),
            lEr = char.substring(0, trackErased), // labels left of the erased track 
            rEr = char.substring(trackErased); // labels right of the erased track   

        for (var j = 0; j < sigma; j++)
            res[i].push(charInd(lEr + j + rEr));
    }

    return res;
}


function rabinScott(T, tracksErased) {
    var states = { '0': 0 }, // map from hashes of sets of states of old machine to their label
        Tnew = {
            delta: [],
            finalStates: {},
            tracks: T.tracks - 1,
            sc: 0 // number of reachable sets of states added to delta so far
        },
        erasedTo = newCharsToOldChars(Tnew.tracks, tracksErased),
        newAlphabetSize = Math.pow(sigma, Tnew.tracks),
        frontier = ['0']; //queue of new state sets (not yet in delta, but already in states)
        // so frontier[Tnew.sc] is next state needing attention

    while (frontier.length > Tnew.sc) {

        var stateSetHash = frontier[Tnew.sc],
            stateSet = listFromHash(stateSetHash),
            deltaS = getArray(T.sc); // need array that can handle 2^T.sc states

        console.log('\nCurrent State Set: ' + stateSetHash);

        // for each character in our new alphabet
        for (var i = 0, nextStateSet = {}; i < newAlphabetSize; i++) {

            var charIPreimage = erasedTo[i];

            for (var j = 0; j < sigma; j++)
                for (var k = 0, oldCharInd = charIPreimage[j]; k < stateSet.length; k++)
                    nextStateSet[T.delta[stateSet[k]][oldCharInd]] = true;

            var nextStateSetHash = uniqueHash(nextStateSet);
            console.log(`-char ${i} goes to: `, nextStateSetHash);

            // if set we transition to was already seen, map to its index
            if (states[nextStateSetHash] !== undefined)
                deltaS[i] = states[nextStateSetHash];
            else { // otherwise give this new set the next index
                states[nextStateSetHash] = deltaS[i] = frontier.length;
                frontier.push(nextStateSetHash);
            }
        }

        // if it contains a state which was final, this set of states is final
        if (stateSet.some(s => T.finalStates[s]))
            Tnew.finalStates[Tnew.sc] = true;

        Tnew.delta.push(deltaS);
        Tnew.sc++;
    }

    return Tnew;
}

function product(T1, T2, both) {

}

function negate(T) {

}

console.log(binaryAdd)
console.log(isTransducer(binaryAdd))


var res = rabinScott(binaryAdd, 2);

console.log(isTransducer(res))

console.log(res)