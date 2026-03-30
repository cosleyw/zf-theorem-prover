const ND = {
	Arrow: 0,
	Not: 1,
	Ref: 2,
	Gen: 3,
	In: 4
};

const Arrow = (left, right) => ({type: ND.Arrow, left, right});
const Not = (prop) => ({type: ND.Not, prop});
const Ref = (name) => ({type: ND.Ref, name});
const Gen = (arg, body) => ({type: ND.Gen, arg, body});
const In = (member, set) => ({type: ND.In, member, set});

/* //Took up 40% of the runtime...
const is_prop = (term) => {
	switch(term.type){
		case "arrow":
			return is_prop(term.left) && is_prop(term.right);
		case "not":
			return is_prop(term.prop);
		case "ref":
			return false;
		case "gen":
			return term.arg.type == "ref" && is_prop(term.body);
		case "in":
			return term.member.type == "ref" && term.set.type == "ref";
	}

	return false;
};
*/

const free_in = (ref, term) => {
	switch(term.type){
		case ND.Arrow:
			return free_in(ref, term.left) || free_in(ref, term.right);
		case ND.Not:
			return free_in(ref, term.prop);
		case ND.Ref:
			return ref.name == term.name;
		case ND.Gen:
			return term.arg.name != ref.name && free_in(ref, term.body);
		case ND.In:
			return free_in(ref, term.member) || free_in(ref, term.set);
	}

	console.log(term);
	throw new Error("not a prop >:I");
};

const subst = (term, ref, value) => {
	switch(term.type){
		case ND.Arrow: {
			let l = subst(term.left, ref, value);
			let r = subst(term.right, ref, value);

			if(l === term.left && r === term.right)
				return term;
			return Arrow(l, r);
		} case ND.Not: {
			let p = subst(term.prop, ref, value);
			if(p === term.prop)
				return term;
			return Not(p);
		} case ND.Ref: {
			return ref.name == term.name ? value : term;
		} case ND.Gen: {
			if(term.arg.name == ref.name)
				return term;

			if(free_in(term.arg, value)){
				let nr = Ref(Symbol());
				let b = subst(term.body, term.arg, nr);
				if(b === term.body)
					return term;
				return Gen(nr, subst(b, ref, value));
			}

			let b = subst(term.body, ref, value);
			if(b === term.body)
				return term;
			return Gen(term.arg, b);
		} case ND.In: {
			let m = subst(term.member, ref, value);
			let s = subst(term.set, ref, value);

			if(m === term.member && s === term.set)
				return term;
			return In(m, s);
		}
	}

	console.log(term);
	throw new Error("not a prop >:I");
}

export const term_eq = (a, b) => {
	if(a === b)
		return true;

	if(a.type != b.type)
		return false;

	switch(a.type){
		case ND.Arrow:
			return term_eq(a.left, b.left) && term_eq(a.right, b.right);
		case ND.Not:
			return term_eq(a.prop, b.prop);
		case ND.Ref:
			return a.name == b.name;
		case ND.Gen: {
			if(a.arg.name == b.arg.name) //insane speedup somehow... probably due to all of the sharing i do
				return term_eq(a.body, b.body);

			let nr = Ref(Symbol());
			return term_eq(subst(a.body, a.arg, nr), subst(b.body, b.arg, nr));
		} case ND.In:
			return term_eq(a.member, b.member) && term_eq(a.set, b.set);
	}

	console.log(a, b);
	throw new Error("not a prop >:I");
}

const Derived = (prop) => ({type: "derived", prop});
  

const I1 = (a, b) => a && b && a.type == "derived" && a.prop.type == ND.Arrow
	&& b.type == "derived" && term_eq(a.prop.left, b.prop)
	? Derived(a.prop.right)
	: null;

const I2 = (ref, term) => ref && term && ref.type == ND.Ref && term.type == "derived"
	? Derived(Gen(ref, term.prop))
	: null;


const A1 = (a, b) => //is_prop(a) && is_prop(b) ? 
	Derived(Arrow(a, Arrow(b, a)))
	//: null
;

const A2 = (a, b, c) => //is_prop(a) && is_prop(b) && is_prop(c) ? 
	Derived(Arrow(Arrow(a, Arrow(b, c)), Arrow(Arrow(a, b), Arrow(a, c))))
	//: null
;

const A3 = (a, b) => //is_prop(a) && is_prop(b) ? 
	Derived(Arrow(Arrow(Not(a), Not(b)), Arrow(b, a)))
	//: null
;

const A4 = (a, v) => //is_prop(a) && 
	a.type == ND.Gen && v.type == ND.Ref
	? Derived(Arrow(a, subst(a.body, a.arg, v)))
	: null;

const A5 = (x, a, b) => x.type == ND.Ref //&& is_prop(a) && is_prop(b) 
	&& !free_in(x, a)
	? Derived(Arrow(Gen(x, Arrow(a, b)), Arrow(a, Gen(x, b))))
	: null;


const and = (a, b) => Not(Arrow(a, Not(b)));
const or = (a, b) => Arrow(Not(a), b);
const iff = (a, b) => and(Arrow(a, b), Arrow(b, a));
const exists = (x, b) => Not(Gen(x, Not(b)));
const unique = (x, b) => exists(x, and(b, Gen(y, Arrow(subst(b, x, y), Gen(z, iff(In(z, x), In(z, y)))))));


const [a, b, c, d, e, x, y, z, w] = [..."abcdexyzw"].map(Ref);

const Z0 = Derived(exists(x, Gen(y, Not(In(y, x)))));
//extensionality
const Z1 = Derived(Gen(x, Gen(y, Arrow(Gen(z, iff(In(z, x), In(z, y))), Gen(w, iff(In(x, w), In(y, w)))))));
//regularity
const Z2 = Derived(
	Gen(x, Arrow(
		exists(a, In(a, x)),
		exists(y, and(In(y, x), Not(exists(z, and(In(z, y), In(z, x))))))
	))
);
//schema of specification
const Z3 = (z, x, p) => {
	if(z && x && p && z.type == ND.Ref && x.type == ND.Ref /*&& is_prop(p) */){
		let nr = Ref(Symbol());
		return Derived(exists(nr, Gen(x, iff(In(x, nr), and(In(x, z), p)))))
	}
	return null;
};
//axiom of pairing
const Z4 = Derived(Gen(x, Gen(y, exists(z, and(In(x, z), In(y, z)))))); 
//axiom of union
const Z5 = Derived(Gen(w, exists(a, Gen(y, Gen(x, Arrow(and(In(x, y), In(y, w)), In(x, a)))))))

//axiom of replacement
const Z6 = (x, y, a, p) => {
	if(x && y && a && p && x.type == ND.Ref && y.type == ND.Ref && a.type == ND.Ref
	//&& is_prop(p)
	){
		let nr = Ref(Symbol());
		return Derived(Gen(a, Arrow(Gen(x, Arrow(In(x, a), unique(y, p))), 
			subst(
				exists(b, Gen(x, Arrow(In(x, a), exists(y, and(In(y, b), nr))))),
				nr,
				p)
		)));
	}
	return null;
}

//axiom of infinity
//let Succ = (s) => null;
//let Z7 = Derived(exists(x, and(exists(e, Gen(z, and(Not(In(z, e)), In(z, x)))), Gen(y, Arrow(In(y, x), In(Succ(y), x))))));

//axiom of powerset
const Z8 = Derived(Gen(x, exists(y, Gen(z, Arrow(Gen(a, Arrow(In(a, z), In(a, x))), In(z, y))))));


/*


So long as everything before here is correct it shouldn't matter how much crap i add on top


*/

export const zf_rules = {I1, I2, A1, A2, A3, A4, A5, Z0, Z1, Z2, Z3, Z4, Z5, Z6, /* Z7, */ Z8};
export const zf_ast = {ND, Arrow, Not, Ref, Gen, In};

//exports rules, ast, term_eq
