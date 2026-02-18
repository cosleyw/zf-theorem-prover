export const State = (string) => ({string, index: 0, stack: [], fail: false});

export const incSt = (nxt) => (st) => {
	//console.log(st);
	let n_st = {...st};
	n_st.index++;
	return nxt(n_st);
}

export const failSt = (st) => {
	let n_st = {...st};
	n_st.fail = true;
	return n_st;
}

export const pushSt = (v) => (nxt) => (st) => {
	let n_st = {...st};
	n_st.stack = [...st.stack, v];
	return nxt(n_st);
}

export const popSt = (fn) => (nxt) => (st) => {
	let n_st = {...st};
	n_st.stack = [...st.stack];
	return fn(n_st.stack.pop())(nxt)(n_st);
}

export const Take = (chr) => (nxt) => (st) => 
	!st.fail && st.string[st.index] == chr
	? pushSt(chr)(incSt(nxt))(st)
	: failSt(st);

export const Rx = (rx) => (nxt) => (st) => 
	!st.fail && st.string[st.index] && rx.test(st.string[st.index])
	? pushSt(st.string[st.index])(incSt(nxt))(st)
	: failSt(st);



export const Pass = (nxt) => (st) => nxt(st);

export const Either = (f, g) => (nxt) => (st) => {
	let t = f(nxt)(st);
	return t.fail ? g(nxt)(st) : t;
}

export const Both = (f, g) => (nxt) => f(g(nxt))

export const all = (...x) => x.reduce(Both);
export const some = (...x) => x.reduce(Either, (nxt) => failSt);

export const Many = (f) => (nxt) => (st) => {
	let li = [];
	let push_val = popSt(v => (li.push(v), Pass));
	let t = all(f, push_val)(x=>x)(st);
	while(!t.fail){
		let n = all(f, push_val)(x=>x)(t);
		if(n.fail)
			break;
		t = n;
	}

	if(t.fail)
		return t;

	return pushSt(li)(nxt)(t);
	
	//let rec = (nxt) => all(f, popSt(x => popSt(l => pushSt([...l, x]))), Either(rec, Pass))(nxt);
	//return Both(pushSt([]), rec);
}

export const Opt = (f) => Either(f, Pass);
export const Del = all(popSt((x) => Pass));
