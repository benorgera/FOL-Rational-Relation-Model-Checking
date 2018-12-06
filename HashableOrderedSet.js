const hash = require('object-hash');

function HashableOrderedSet() {
	Set.call(this, arguments);

	var arr = Array.from(this);
	arr.sort((a, b) => a - b);

	this.hash = arr.join(',');

	this.getHash = function () {
		return this.hash;
	}

	this.add = function (elem) {

	}
}

module.exports = 