import {ns_get, ns_set, Ns, ns_lookup, ns_flatten} from "./ns.js"
import {zf_rules, zf_ast, term_eq} from "./zf.js"
import {print_term, ZF, ZF_unit, zf_parse} from "./syntax.js";
import { deduce as builtin_deduce } from "./check.js";

let App = (func, arg) => ({type:"app", func, arg});

let Arrow = zf_ast.Arrow;
let Not = zf_ast.Not;
let Ref = zf_ast.Ref;
let Gen = zf_ast.Gen;
let In = zf_ast.In;

let NSref = (name) => ({type: "ns_ref", name});
let Lam = (arg, body) => ({type:"lam", arg, body});
let Rule = (name, fn, n_args, args = []) => ({type: "rule", name, fn, args, n_args});
let Dlam = (arg, arg_type, body) => ({type:"dlam", arg, arg_type, body});
let Match = (arg, cases) => ({type:"match", arg, cases});
let Exact = (prop) => ({type:"exact", prop});

const and = (a, b) => Not(Arrow(a, Not(b)));
const iff = (a, b) => and(Arrow(a, b), Arrow(b, a));
const exists = (x, b) => Not(Gen(x, Not(b)));

const partial_deduction = (prop, term) => ({type:"partial_deduction", term, prop});
const deduction = (prop, proof) => {
	if(proof == null){ throw new Error("not a proof"); }
	return {type:"deduction", prop, proof}; 
};

const axiom_props = {
	Z0: ZF`!\\/x.!\\/y.!y#x`,
	Z1: ZF`\\/x.\\/y.(\\/z.!((z#x->z#y)->!(z#y->z#x)))->(\\/z.!((x#z->y#z)->!(y#z->x#z)))`,
	Z2: ZF`\\/x.(!\\/a.!a#x)->(!\\/y.!!(y#x->!!(!\\/z.!!(z#y->!z#x))))`,
	Z4: ZF`\\/x. \\/y.!\\/z.!!(x#z->!y#z)`,
	Z5: ZF`\\/w. !\\/a.!\\/y.\\/x.!(x#y->!y#w)->x#a`,
	Z8: ZF`\\/x.!\\/y.!\\/z.(\\/a.a#z->a#x)->z#y`
};



let memoize = (fn) => {
	let memo = new Map();
	return (x) => {
		//return memo.getOrInsertComputed(key, fn);
		
		let ret;
		if((ret = memo.get(x)) != null)
			return ret

		memo.set(x, ret = fn(x));
		//memo.set(ret, ret = fn(x));
		return ret;
	}
}


let pattern_fv = (term) => {
	switch(term.type){
		case zf_ast.ND.Ref: {
			let env = new Map();
			env.set(term.name, Ref(Symbol()));
			return env;
		} case zf_ast.ND.Arrow: {
			let e1 = pattern_fv(term.left);
			let e2 = pattern_fv(term.right);
			return new Map([...e1, ...e2]);
		} case zf_ast.ND.In: {
			let e1 = pattern_fv(term.member);
			let e2 = pattern_fv(term.set);
			return new Map([...e1, ...e2]);
		} case zf_ast.ND.Gen: {
			let e1 = pattern_fv(term.body);
			e1.delete(term.arg.name);
			return e1;
		} case zf_ast.ND.Not:
			return pattern_fv(term.prop);
		case "exact":
			return new Map();
	}

	console.log(term);
	throw new Error("cannot find pattern free variables");
}




export let deduce = (ns, term, dtype) => {


//--- TODO rewrite?

let subst = (term, x, val) => {
	switch(term.type){
		case "dlam": {
			let type = subst(term.arg_type, x, val);
			if(term.arg.name != x.name){
				if(typeof term.arg.name == "symbol")
					return Dlam(term.arg, type, subst(term.body, x, val));

				let nr = Ref(Symbol());
				return Dlam(nr, type, subst(subst(term.body, term.arg, nr), x, val));
			}

			if (type === term.arg_type) {
				return term;
			}
			return Dlam(term.arg, type, term.body);
		}

		case zf_ast.ND.Gen:
			if(term.arg.name != x.name){
				if(typeof term.arg.name == "symbol")
					return Gen(term.arg, subst(term.body, x, val));

				let nr = Ref(Symbol());
				return Gen(nr, subst(subst(term.body, term.arg, nr), x, val));
			}
			return term;

		case "lam":
			if(term.arg.name != x.name){
				if(typeof term.arg.name == "symbol")
					return Lam(term.arg, subst(term.body, x, val));

				let nr = Ref(Symbol());
				return Lam(nr, subst(subst(term.body, term.arg, nr), x, val));
			}
			return term;

		case "app": {
			let newFunc = subst(term.func, x, val);
			let newArg = subst(term.arg, x, val);

			if (newFunc === term.func && newArg === term.arg) {
				return term;
			}
			return App(newFunc, newArg);
		}

		case zf_ast.ND.Arrow: {
			let newLeft = subst(term.left, x, val);
			let newRight = subst(term.right, x, val);

			if (newLeft === term.left && newRight === term.right) {
				return term;
			}
			return Arrow(newLeft, newRight);
		}

		case zf_ast.ND.Not: {
			let newProp = subst(term.prop, x, val);

			if (newProp === term.prop) { return term; }
			return Not(newProp);
		}

		case zf_ast.ND.Ref:
			if(term.name == x.name) { return val; }
			return term;
		case zf_ast.ND.In: {
			let newMember = subst(term.member, x, val);
			let newSet = subst(term.set, x, val);

			if (newMember === term.member && newSet === term.set) {
				return term;
			}
			return In(newMember, newSet);
		}
		case "match":
			if(term.arg.name != x.name){
				if(typeof term.arg.name == "symbol"){
					return Match(term.arg, term.cases.map(([pattern, body]) => 
						[match_exact_subst(pattern, x, val), subst(body, x, val)]));
				}


				let nr = Ref(Symbol());
				let newCases = term.cases.map(([pattern, body]) => {
					let rp = Reduce(pattern); //uses NS here...
					let fv = pattern_fv(rp);

					let [p, b] = [...fv].reduce(([pattern, body], [name, sym]) =>
						[subst(pattern, Ref(name), sym), subst(body, Ref(name), sym)]
					, [rp, body]);

					return [match_exact_subst(p, x, val),
						subst(subst(b, term.arg, nr), x, val)];
				});

				return Match(nr, newCases);
			}
			return term;

		case "rule":
		case "exact":
		case "deduction":
		case "partial_deduction":
		case "level":
			return term;
		case "ns_ref": {
			let t1 = ns_get(ns, term);
			let ret = subst(t1, x, val);

			if(ret === t1)
				return term;
			return ret;
		}
	}

	console.log(term);
	throw new Error("cannot subst");
}

let Reduce = memoize((term) => {
	switch(term.type){
		case "ns_ref":
			return ns_get(ns, term);
		case "app":
			let func = Reduce(term.func);
			switch(func.type){
				case "lam":
				case zf_ast.ND.Gen: {
					let arg = Reduce(term.arg);
					return Reduce(subst(func.body, func.arg, arg));
				} case zf_ast.ND.Arrow:
					return func.right;
			}

			if(func === term.func){ return term; }
			return App(func, term.arg);
		case zf_ast.ND.Arrow: {
			let lv = Reduce(term.left);
			let rv = Reduce(term.right);
			if(lv === term.left && rv === term.right){ return term; }
			return Arrow(lv, rv);
		} case "exact": {
			let pv = Reduce(term.prop);
			if(pv === term.prop) { return term; }
			return Exact(pv);
		} case zf_ast.ND.Not: {
			let pv = Reduce(term.prop);
			if(pv === term.prop) { return term; }
			return Not(pv);
		} case zf_ast.ND.Gen: {
			let bv = Reduce(term.body);
			if(bv === term.body){ return term; }
			return Gen(term.arg, bv);
		} case zf_ast.ND.In: {
			let lv = Reduce(term.member);
			let rv = Reduce(term.set);
			if(lv === term.member && rv === term.set){ return term; }
			return In(lv, rv);
		} 
		case zf_ast.ND.Ref:
		case "lam":
		case "rule":
		case "deduction":
		case "partial_deduction":
		case "dlam":
		case "match":
			return term;
	}

	console.log(term);
	throw new Error("cannot reduce");
});








let reduce_redex = memoize((term) => {
	switch(term.type){
		case "ns_ref":
			return ns_get(ns, term);
		case "app":
			let func = reduce_redex(term.func);
			switch(func.type){
				case "lam":
				case zf_ast.ND.Gen: {
					let arg = term.arg;
					return reduce_redex(subst(func.body, func.arg, arg));
				} case zf_ast.ND.Arrow:
					return reduce_redex(func.right)
			}

			if(func === term.func)
				return term;

			return App(func, term.arg);
		case "lam":
		case zf_ast.ND.Ref:
		case zf_ast.ND.Arrow:
		case zf_ast.ND.Not:
		case zf_ast.ND.Gen:
		case zf_ast.ND.In:
			return term;
	}

	console.log(term);
	throw new Error("cannot reduce");
})


let match_exact_subst = (term, x, val) => {
	switch(term.type){
		case zf_ast.ND.Ref:
			return term;
		case zf_ast.ND.Arrow:
			return Arrow(match_exact_subst(term.left, x, val), match_exact_subst(term.right, x, val));
		case zf_ast.ND.In:
			return In(match_exact_subst(term.member, x, val), match_exact_subst(term.set, x, val));
		case zf_ast.ND.Gen: {
			if(term.arg.name != x.name){
				if(typeof term.arg.name == "symbol")
					return Gen(term.arg, match_exact_subst(term.body, x, val));

				let nr = Ref(Symbol());
				return Gen(nr, match_exact_subst(match_exact_subst(subst(term.body, term.arg, nr), term.arg, nr), x, val));
			}

			return term;
		} case zf_ast.ND.Not:
			return Not(match_exact_subst(term.prop, x, val));
		case "exact":
			return Exact(subst(term.prop, x, val));
	}


	throw new Error("cannot substitute in pattern");
}

let unify_mp = (t1, t2) => {
	let uvars = {};
	let vals = {};

	let unify = (t1, t2) => {
		if(t1.type != t2.type)
			return false;
	
		switch(t1.type){
			case zf_ast.ND.Ref: {
				if(uvars[t1.name] != null){
					if(vals[t1.name])
						return vals[t1.name].name == t2.name;

					vals[t1.name] = t2;
					return true;
				}
			
				return t1.name == t2.name;
			} case zf_ast.ND.Arrow:
				return unify(t1.left, t2.left, uvars, vals) && unify(t1.right, t2.right, uvars, vals);
			case zf_ast.ND.Gen:
				if(t1.arg == t2.arg)
					return unify(t1.body, t2.body, uvars, vals);
				if(typeof t1.arg == "symbol")
					return unify(t1.body, subst(t2.body, t2.arg, t1.arg), uvars, vals);
				if(typeof t2.arg == "symbol")
					return unify(subst(t1.body, t1.arg, t2.arg), t2.body, uvars, vals);
				let nr = Ref(Symbol());
				return unify(subst(t1.body, t1.arg, nr), subst(t2.body, t2.arg, nr), uvars, vals);
			case zf_ast.ND.Not:
				return unify(t1.prop, t2.prop, uvars, vals);
			case zf_ast.ND.In:
				return unify(t1.member, t2.member, uvars, vals) && unify(t1.set, t2.set, uvars, vals);
		}


		console.log(term);
		throw new Error("cannot unify");
	}

	let count = 0;
	let tp = Reduce(t1.prop);
	while(tp.type == zf_ast.ND.Gen){
		uvars[tp.arg.name] = count++;
		tp = tp.body;
	}

	if(tp.type != zf_ast.ND.Arrow)
		throw new Error("cannot unify_mp");

	if(unify(tp.left, Reduce(t2.prop))){
		let proof = t1;
		let unassigned = [];
		let prop = Reduce(t1.prop);
		let count = 0;
		while(prop.type == zf_ast.ND.Gen){
			if(uvars[prop.arg.name] == count && vals[prop.arg.name]){
				proof = App(proof, vals[prop.arg.name]);
			}else{
				let nr = Ref(Symbol());
				proof = App(proof, nr);
				unassigned.push(nr);
			}

			count++;
			prop = prop.body;
		}

		proof = App(proof, t2);

		while(unassigned.length){
			let arg = unassigned.pop();
			proof = Gen(arg, proof);
		}


		return proof;
	}


	throw new Error("cannot unify_mp");
}



//---- TODO end


let zf_rules = 
{	I1:  ns_get(ns, NSref(["I1"])).fn,
	I2:  ns_get(ns, NSref(["I2"])).fn,
	A1:  ns_get(ns, NSref(["A1"])).fn,
	A2:  ns_get(ns, NSref(["A2"])).fn,
	A3:  ns_get(ns, NSref(["A3"])).fn,
	A4:  ns_get(ns, NSref(["A4"])).fn,
	A5:  ns_get(ns, NSref(["A5"])).fn,
	Z0:  ns_get(ns, NSref(["Z0"])).fn,
	Z1:  ns_get(ns, NSref(["Z1"])).fn,
	Z2:  ns_get(ns, NSref(["Z2"])).fn,
	Z3:  ns_get(ns, NSref(["Z3"])).fn,
	Z4:  ns_get(ns, NSref(["Z4"])).fn,
	Z5:  ns_get(ns, NSref(["Z5"])).fn,
	Z6:  ns_get(ns, NSref(["Z6"])).fn,
	Z8:  ns_get(ns, NSref(["Z8"])).fn,
	"_":  ns_get(ns, NSref(["_"])).fn };

let rules = {
	I1: (a, b) => {
		//console.log("A4: ", [a, b].map(k => print_term(k)));
		let t = a.prop.type == zf_ast.ND.Arrow ? a.prop.right : App(a.prop, b.prop);
		if(a.type == "deduction" && b.type == "deduction")
			return deduction(t, zf_rules.I1(a.proof, b.proof));
		return partial_deduction(t, App(a, b));
	},
	I2: (x, t) => {
		if(t.type == "deduction")
			return deduction(Gen(x, t.prop), zf_rules.I2(x, t.proof));
		return partial_deduction(Gen(x, t.prop), Gen(x, t));
	},
	A1: (a, b) => {
		return deduction(Arrow(a, Arrow(b, a)), 
			zf_rules.A1(Reduce(a), Reduce(b)));
	},
	A2: (a, b, c) => {
		return deduction(Arrow(Arrow(a, Arrow(b, c)), Arrow(Arrow(a, b), Arrow(a, c))), 
			zf_rules.A2(Reduce(a), Reduce(b), Reduce(c)));
	},
	A3: (a, b) => { 
		return deduction(Arrow(Arrow(Not(a), Not(b)), Arrow(b, a)), 
			zf_rules.A3(Reduce(a), Reduce(b)));
	},
	A4: (a, v) => {
		return deduction(Arrow(a, a.type == zf_ast.ND.Gen ? subst(a.body, a.arg, v) : App(a, v)),
			zf_rules.A4(Reduce(a), v));
	},
	A5: (x, a, b) => {
		return deduction(Arrow(Gen(x, Arrow(a, b)), Arrow(a, Gen(x, b))), 
			zf_rules.A5(x, Reduce(a), Reduce(b)));
	},
	Z0: (t => () => t)(deduction(axiom_props.Z0,zf_rules.Z0)),
	Z1: (t => () => t)(deduction(axiom_props.Z1, zf_rules.Z1)),
	Z2: (t => () => t)(deduction(axiom_props.Z2, zf_rules.Z2)),
	Z3: (z, x, p) => {
		let nr = Ref(Symbol());
		return deduction(
			exists(nr, Gen(x, iff(In(x, nr), and(In(x, z), p)))),
			zf_rules.Z3(z, x, Reduce(p)));
	},
	Z4: (t => () => t)(deduction(axiom_props.Z4, zf_rules.Z4)),
	Z5: (t => () => t)(deduction(axiom_props.Z5, zf_rules.Z5)),
	Z6: null,
	//Z7: null,
	Z8: (t => () => t)(deduction(axiom_props.Z8, zf_rules.Z8)),
	"_": (a) => Ref(Symbol(a))
};


let thid = (a) => rules.I1(rules.I1(rules.A2(a,Arrow(a,a),a),rules.A1(a,Arrow(a,a))),rules.A1(a,a));





let fill_pattern = (pattern, term, env, bound = {}, hs = []) => {
	if(!(pattern.type == zf_ast.ND.Ref || pattern.type == "exact") && pattern.type != term.type){
		term = reduce_redex(term);
		if(!(pattern.type == zf_ast.ND.Ref || pattern.type == "exact") && pattern.type != term.type)
			return false;
	}
	

	switch(pattern.type){
		case zf_ast.ND.Ref: {
			if(bound[pattern.name]){
				let t = Reduce(term);
				return t.type == zf_ast.ND.Ref && pattern.name == t.name;
			};

			let lam = hs.reduceRight((a, b) => Lam(b, a), term);
			if(env.get(pattern.name) == null)
				env.set(pattern.name, lam);

			let eq = (t1, t2) => {
				if(t1.type == t2.type && t1.type == "lam")
					return term_eq(t1.arg, t2.arg) && eq(t1.body, t2.body);
				return term_eq(Reduce(t1), Reduce(t2));
			}

			return eq(env.get(pattern.name), lam);
		} case zf_ast.ND.Arrow:
			return fill_pattern(pattern.left, term.left, env, bound, hs) 
				&& fill_pattern(pattern.right, term.right, env, bound, hs);
		case zf_ast.ND.In:
			return fill_pattern(pattern.member, term.member, env, bound, hs) 
				&& fill_pattern(pattern.set, term.set, env, bound, hs);
		case zf_ast.ND.Gen: {
			let n_bound = {...bound};
			n_bound[pattern.arg.name] = true;
			return fill_pattern(pattern.body, subst(term.body, term.arg, pattern.arg), env, 
				n_bound, [...hs, pattern.arg]);
		} case zf_ast.ND.Not: {
			return fill_pattern(pattern.prop, term.prop, env, bound, hs);
		} case "exact": 
			return term_eq(pattern.prop, Reduce(term));
	}
}

let ctx_level = (level, deduction) => ({type: "level", level, deduction});

let deduce = (term) => {
	let bound = {};

	let taut_ref = Ref(Symbol());
	let taut = Arrow(In(taut_ref, taut_ref), In(taut_ref, taut_ref));
	let taut_proof = thid(In(taut_ref, taut_ref));

	let hs = [taut];
	let jt = [{}];


	let ac = (a, b) => builtin_deduce(ns, App(App(NSref(["__builtin__", "ac"]), a), b));
	let and_l = (a) => builtin_deduce(ns, App(NSref(["__builtin__", "and_l"]), a));
	let and_r = (a) => builtin_deduce(ns, App(NSref(["__builtin__", "and_r"]), a));
	let unpack = (a) => builtin_deduce(ns, App(NSref(["__builtin__", "unpack"]), a));

	//l1 bigger
	let connect_up = (l1, l2) => {
		let diff = l1 - l2;
		if(jt[l1][diff] != null)
			return jt[l1][diff];
		if(l1 == l2)
			return jt[l1][diff] = thid(hs[l1]);
		if(l1 == l2 + 1){
			//console.log(print_term(hs[l1]));
			return jt[l1][diff] = and_l(hs[l1]);
		}

		let p1 = connect_up(l1, l2+1);
		let p2 = connect_up(l2+1, l2);

		return jt[l1][diff] = ac(p1, p2);
	}

	let connect_down = (l1, l2) => {
		let diff = l1 - l2;
		if(jt[l1][diff] != null)
			return jt[l1][diff];

		if(l1 == l2)
			return jt[l1][diff] = thid(hs[l1]);
		if(l1 == l2 + 1)
			return jt[l1][diff] = and_l(hs[l1]);

		let p1 = connect_down(l1, l1-1);
		let p2 = connect_down(l1-1, l2);

		//console.log([p1, p2].map(v => print_term(v.proof)));

		return jt[l1][diff] = ac(p1, p2);
	}

	let transport = (l1, l2) => {
		if(l2 > l1)
			throw new Error("huh?");
		let diff = l1 - l2;
		if(jt[l1][diff] != null)
			return jt[l1][diff];
		if(l1 == l2)
			return jt[l1][diff] = thid(hs[l1]);
		if(l1 == l2 + 1)
			return jt[l1][diff] = and_l(hs[l1]);

		let q = 1 << (31 - Math.clz32(l1 ^ l2));
		let cut = l1 & ~(q - 1);

		//console.log(l1, cut, l2);
		let p1 = connect_down(l1, cut);
		let p2 = connect_up(cut, l2);

		return jt[l1][diff] = ac(p1, p2);
	}

	let deduce_ = (term, bound = {}) => {
		switch(term.type){
			case zf_ast.ND.Ref: {
				if(bound[term.name] == null)
					return term;

				let level = bound[term.name];
				return ctx_level(level, and_r(hs[level]));
			} case "ns_ref": {
				let val = ns_get(ns, term);
				if(val == null) throw new Error(print_term(term) + " not defined :/");
				return deduce_(val, hs);
			} case "dlam": {
				let n_bound = {...bound};
				n_bound[term.arg.name] = hs.length;
				
				let cl = hs.length - 1;
				hs.push(and(hs.at(-1), term.arg_type));
				jt.push({});

				let {level, deduction} = deduce_(term.body, n_bound);

				hs.pop();
				jt.pop();

				return ctx_level(cl, unpack(deduction));
			} case zf_ast.ND.Gen: {
				let body = deduce_(term.body, bound);

				if(body.type == "level"){
					return ctx_level(body.level, 
						rules.I1(rules.A5(term.arg, hs[body.level], body.deduction.prop.right), 
							rules.I2(term.arg, body.deduction)));
				}

				return Gen(term.arg, body);
			} case "rule": {
				if(term.n_args == 0)
					return deduce_(rules[term.name](), bound);

				return term;
			} case "app": {
				let p1 = deduce_(term.func, bound);
				let p2 = deduce_(term.arg, bound);

				//console.log([p1, p2].map(v => [v.type, print_term(v.deduction ?? v)]));

				switch(p1.type){
				case "lam": {
					if(typeof p1.arg.name != "symbol"){
						let nr = Ref(Symbol());
						return deduce_(subst(subst(p1.body, p1.arg, nr), nr, p2), bound); 
					}
					return deduce_(subst(p1.body, p1.arg, p2), bound);
				} case "level": {
					let cl = hs.length - 1;

					let ft = Reduce(p1.deduction.prop.right);
					//console.log("hi", ft.type, zf_ast.ND.Arrow);
					//console.log(p1.deduction.prop.right.type, zf_ast.ND.Arrow);
					if(ft.type == zf_ast.ND.Arrow){
						//console.log([term.func, p1.deduction].map(print_term));

						let c1 = transport(cl, p1.level);
						let c2 = transport(cl, p2.level);

						let F = ac(c1, p1.deduction);
						let A = ac(c2, p2.deduction);
						let P = rules.A2(hs[cl], p2.deduction.prop.right, 
							p1.deduction.prop.right.type == zf_ast.ND.Arrow
							? p1.deduction.prop.right.right
							: App(p1.deduction.prop.right, p2.deduction.prop.right)
						);

						return ctx_level(cl, rules.I1(rules.I1(P, F), A));
					}

					if(ft.type == zf_ast.ND.Gen){
						if(p2.type == zf_ast.ND.Ref){
							//console.log("huh?");
							return ctx_level(p1.level,
								ac(p1.deduction, rules.A4(p1.deduction.prop.right, p2)));
						}

						throw new Error("not done :/");
					}

					break;
				} case "rule": {
					let nr = Rule(p1.name, p1.fn, p1.n_args, [...p1.args, p2]);
					if(nr.n_args == nr.args.length)
						return deduce_(rules[nr.name](...nr.args), bound);
					return nr;
				} case "match": {
					for(let i = 0; i < p1.cases.length; i++){
						let [pattern, body] = p1.cases[i];

						let env = new Map();

						if(fill_pattern(Reduce(pattern), p2.type == "level" 
							? p2.deduction.prop.right : p2, env)){
							//console.log("pattern", [pattern, arg.prop, Reduce(arg.prop)].map(print_term), env);
							let v = [...env].reduceRight((a, [x, val]) => Lam(Ref(x), a), body);
							v = [...env].reduce((a, [x, val]) => App(a, val), App(Lam(p1.arg, v), p2));

							//console.log(print_term(v));
							return deduce_(v, bound);
						}
					}
					break;
				} 
				}

				console.log("app failed :/");
				break;
			}case "lam":
			case zf_ast.ND.Not:
			case zf_ast.ND.In:
			case zf_ast.ND.Arrow:
			case "match":
			case "level":
				return term;
			case "deduction": {
				let cl = hs.length - 1;
				return ctx_level(cl, 
					rules.I1(rules.A1(term.prop, hs[cl]), term));
			}
					
		}
		console.log(term);
		throw new Error("could not deduce :/");
	}

	let ret = deduce_(term, bound);
	//console.log(ret);
	return rules.I1(ret.deduction, taut_proof);
}



	let ret = deduce(term);


	if(dtype){
		if(term_eq(Reduce(ret.prop), Reduce(dtype))){
			return deduction(dtype, ret.proof);
		}

		console.log(print_term(Reduce(ret.prop)), print_term(Reduce(dtype)))
		throw new Error("did not match expected type");
	}

	
	return ret;	

}





