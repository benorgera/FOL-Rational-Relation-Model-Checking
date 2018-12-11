function empty(queue) {
	return queue.e;
}

function enq(queue, elem) {
	if (queue.e) {
		queue.h = queue.t = { d: elem, p: null, n: null };
		queue.e = false;
	} else
	    queue.t = queue.t.n = { d: elem, p: queue.t, n: null };
}

function deq(queue) {
	if (queue.e)
		return null;

	var data = queue.h.d;
	queue.h = queue.h.n;

	if (queue.h === null) {
		queue.t = null;
		queue.e = true;
	} else
		queue.h.p = null;

	return data;
}

function singleton(elem) {
	var queue = { h: null, t: null, e: true };
	enq(queue, elem);
	return queue;
}

module.exports = { empty, enq, deq, singleton };