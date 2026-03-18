import {ns_get, ns_set, Ns, ns_lookup} from "./ns.js"
import {zf_rules, term_eq} from "./zf.js"
import {print_term, ZF, ZF_unit, zf_parse} from "./syntax.js";

let App = (func, arg) => ({type:"app", func, arg});
let Arrow = (left, right) => ({type: "arrow", left, right});
let Not = (prop) => ({type:"not", prop});
let Ref = (name) => ({type: "ref", name});
let Gen = (arg, body) => ({type:"gen", arg, body});
let In = (member, set) => ({type:"in", member, set});

let NSref = (name) => ({type: "ns_ref", name});
let Lam = (arg, body) => ({type:"lam", arg, body});
let Rule = (name, fn, n_args, args = []) => ({type: "rule", name, fn, args, n_args});
let Dlam = (arg, arg_type, body) => ({type:"dlam", arg, arg_type, body});
let Match = (arg, cases) => ({type:"match", arg, cases});
let Exact = (prop) => ({type:"exact", prop});

const and = (a, b) => Not(Arrow(a, Not(b)));
const iff = (a, b) => and(Arrow(a, b), Arrow(b, a));
const exists = (x, b) => Not(Gen(x, Not(b)));





export let deduce = (ns, term, dtype) => {


//--- TODO rewrite?

let subst = (term, x, val) => {
	switch(term.type){
		case "ns_ref":
			return term;

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

		case "gen":
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

		case "arrow": {
			let newLeft = subst(term.left, x, val);
			let newRight = subst(term.right, x, val);

			if (newLeft === term.left && newRight === term.right) {
				return term;
			}
			return Arrow(newLeft, newRight);
		}

		case "not": {
			let newProp = subst(term.prop, x, val);

			if (newProp === term.prop) {
				return term;
			}
			return Not(newProp);
		}

		case "ref":
			if(term.name == x.name)
				return val;
			return term;
		case "in": {
			let newMember = subst(term.member, x, val);
			let newSet = subst(term.set, x, val);

			if (newMember === term.member && newSet === term.set) {
				return term;
			}
			return In(newMember, newSet);
		}

		case "rule":
			return term;

		case "match":
			if(term.arg.name != x.name){
				if(typeof term.arg.name == "symbol"){
					return Match(term.arg, term.cases.map(([pattern, body]) => 
						[match_exact_subst(pattern, x, val), subst(body, x, val)]));
				}


				let nr = Ref(Symbol());
				let newCases = term.cases.map(([pattern, body]) => {
					let rp = Reduce(pattern);
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

		case "exact":
		case "deduction":
		case "partial_deduction":
			return term;
	}

	console.log(term);
	throw new Error("cannot subst");
}


let __reduce_memo = new Map();
let Reduce = (term) => {
	let reduce = (term) => {
		switch(term.type){
			case "ns_ref":
				return ns_get(ns, term);
			case "ref":
			case "lam":
				return term;
			case "app":
				let func = Reduce(term.func);
				let arg = Reduce(term.arg);
				switch(func.type){
					case "lam":
						return Reduce(subst(func.body, func.arg, arg));
					case "gen":
						return Reduce(subst(func.body, func.arg, arg));
					case "arrow":
						return func.right;
				}

				if(func === term.func && arg === term.arg){
					return term;
				}

				return App(func, arg);
			case "arrow": {
				let lv = Reduce(term.left);
				let rv = Reduce(term.right);
				if(lv === term.left && rv === term.right){
					return term;
				}

				return Arrow(lv, rv);
			} case "exact": {
				let pv = Reduce(term.prop);
				if(pv === term.prop) {
					return term;
				}

				return Exact(pv);
			} case "not": {
				let pv = Reduce(term.prop);
				if(pv === term.prop) {
					return term;
				}

				return Not(pv);
			} case "gen": {
				let bv = Reduce(term.body);
				if(bv === term.body){
					return term;
				}

				return Gen(term.arg, bv);
			} case "in": {
				let lv = Reduce(term.member);
				let rv = Reduce(term.set);
				if(lv === term.member && rv === term.set){
					return term;
				}

				return In(lv, rv);
			} case "rule":
				return term;
			case "deduction":
			case "partial_deduction":
			case "dlam":
			case "match":
				return term;
		}

		console.log(term);
		throw new Error("cannot reduce");
	}

	if(__reduce_memo.has(term))
		return __reduce_memo.get(term);

	let ret = reduce(term);
	__reduce_memo.set(term, ret);
	return ret;
}








//---- TODO redo match logic?

let __redex_memo = new Map();
let reduce_redex = (term) => {
let reduce_red = (term) => {
	//console.log("redex:", term);
	switch(term.type){
		case "ns_ref":
			return ns_get(ns, term);
		case "ref":
			return term;
		case "app":
			let func = reduce_redex(term.func);
			let arg = term.arg;
			switch(func.type){
				case "lam":
				case "gen":
					return reduce_redex(subst(func.body, func.arg, arg));
				case "arrow":
					return reduce_redex(func.right)
			}

			return App(func, arg);
		case "lam":
		case "arrow":
		case "not":
		case "gen":
		case "in":
			return term;
	}

	console.log(term);
	throw new Error("cannot reduce");
}

	if(__redex_memo.has(term))
		return __redex_memo.get(term);

	let ret = reduce_red(term);
	__redex_memo.set(term, ret);
	return ret;
}

let match_exact_subst = (term, x, val) => {
	switch(term.type){
		case "ref":
			return term;
		case "arrow":
			return Arrow(match_exact_subst(term.left, x, val), match_exact_subst(term.right, x, val));
		case "in":
			return In(match_exact_subst(term.member, x, val), match_exact_subst(term.set, x, val));
		case "gen": {
			if(term.arg.name != x.name){
				if(typeof term.arg.name == "symbol")
					return Gen(term.arg, match_exact_subst(term.body, x, val));

				let nr = Ref(Symbol());
				return Gen(nr, match_exact_subst(match_exact_subst(subst(term.body, term.arg, nr), term.arg, nr), x, val));
			}

			return term;
		} case "not":
			return Not(match_exact_subst(term.prop, x, val));
		case "exact":
			return Exact(subst(term.prop, x, val));
	}


	throw new Error("cannot substitute in pattern");
}

let pattern_fv = (term) => {
	switch(term.type){
		case "ref": {
			let env = new Map();
			env.set(term.name, Ref(Symbol()));
			return env;
		} case "arrow": {
			let e1 = pattern_fv(term.left);
			let e2 = pattern_fv(term.right);
			return new Map([...e1, ...e2]);
		} case "in": {
			let e1 = pattern_fv(term.member);
			let e2 = pattern_fv(term.set);
			return new Map([...e1, ...e2]);
		} case "gen": {
			let e1 = pattern_fv(term.body);
			e1.delete(term.arg.name);
			return e1;
		} case "not":
			return pattern_fv(term.prop);
		case "exact":
			return new Map();
	}

	console.log(term);
	throw new Error("cannot find pattern free variables");
}


let unify_mp = (t1, t2) => {
	let uvars = {};
	let vals = {};

	let unify = (t1, t2) => {
		if(t1.type != t2.type)
			return false;
	
		switch(t1.type){
			case "ref": {
				if(uvars[t1.name] != null){
					if(vals[t1.name])
						return vals[t1.name].name == t2.name;

					vals[t1.name] = t2;
					return true;
				}
			
				return t1.name == t2.name;
			} case "arrow":
				return unify(t1.left, t2.left, uvars, vals) && unify(t1.right, t2.right, uvars, vals);
			case "gen":
				let nr = Ref(Symbol());
				return unify(subst(t1.body, t1.arg, nr), subst(t2.body, t2.arg, nr), uvars, vals);
			case "not":
				return unify(t1.prop, t2.prop, uvars, vals);
			case "in":
				return unify(t1.member, t2.member, uvars, vals) && unify(t1.set, t2.set, uvars, vals);
		}


		console.log(term);
		throw new Error("cannot unify");
	}

	let count = 0;
	let tp = Reduce(t1.prop);
	while(tp.type == "gen"){
		uvars[tp.arg.name] = count++;
		tp = tp.body;
	}

	if(tp.type != "arrow")
		throw new Error("cannot unify_mp");

	if(unify(tp.left, Reduce(t2.prop))){
		let proof = t1;
		let unassigned = [];
		let prop = Reduce(t1.prop);
		let count = 0;
		while(prop.type == "gen"){
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


let partial_deduction = (prop, term) => ({type:"partial_deduction", term, prop});
let deduction = (prop, proof) => {
	if(proof == null){ throw new Error("not a proof"); }
	return {type:"deduction", prop, proof}; 
};


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
		let t = a.prop.type == "arrow" ? a.prop.right : App(a.prop, b.prop);
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
		return deduction(Arrow(a, a.type == "gen" ? subst(a.body, a.arg, v) : App(a, v)),
			zf_rules.A4(Reduce(a), v));
	},
	A5: (x, a, b) => {
		return deduction(Arrow(Gen(x, Arrow(a, b)), Arrow(a, Gen(x, b))), 
			zf_rules.A5(x, Reduce(a), Reduce(b)));
	},
	Z0: (t => () => t)(deduction(ZF`!\\/x.!\\/y.!y#x`,zf_rules.Z0)),
	Z1: (t => () => t)(deduction(ZF`\\/x.\\/y.(\\/z.!((z#x->z#y)->!(z#y->z#x)))->(\\/z.!((x#z->y#z)->!(y#z->x#z)))`, zf_rules.Z1)),
	Z2: (t => () => t)(deduction(ZF`\\/x.(!\\/a.!a#x)->(!\\/y.!!(y#x->!!(!\\/z.!!(z#y->!z#x))))`, zf_rules.Z2)),
	Z3: (z, x, p) => {
		let nr = Ref(Symbol());
		return deduction(
			exists(nr, Gen(x, iff(In(x, nr), and(In(x, z), p)))),
			zf_rules.Z3(z, x, Reduce(p)));
	},
	Z4: (t => () => t)(deduction(ZF`\\/x. \\/y.!\\/z.!!(x#z->!y#z)`, zf_rules.Z4)),
	Z5: (t => () => t)(deduction(ZF`\\/w. !\\/a.!\\/y.\\/x.!(x#y->!y#w)->x#a`, zf_rules.Z5)),
	Z6: null,
	//Z7: null,
	Z8: (t => () => t)(deduction(ZF`\\/x.!\\/y.!\\/z.(\\/a.a#z->a#x)->z#y`, zf_rules.Z8)),
	"_": (a) => Ref(Symbol(a))
};


let thid = (a) => rules.I1(rules.I1(rules.A2(a, Arrow(a, a), a), rules.A1(a, Arrow(a, a))), rules.A1(a, a));





let fill_pattern = (pattern, term, env, bound = {}, hs = []) => {
	//console.log("fill: ", print_term(pattern), print_term(term));
	//console.log("fill_pattern: ", print_term(pattern), print_term(term));
	if(!(pattern.type == "ref" || pattern.type == "exact") && pattern.type != term.type){
		term = reduce_redex(term);
		if(!(pattern.type == "ref" || pattern.type == "exact") && pattern.type != term.type)
			return false;
	}
	

	switch(pattern.type){
		case "ref": {
			if(bound[pattern.name]){
				let t = Reduce(term);
				return t.type == "ref" && pattern.name == t.name;
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
		} case "arrow":
			return fill_pattern(pattern.left, term.left, env, bound, hs) 
				&& fill_pattern(pattern.right, term.right, env, bound, hs);
		case "in":
			return fill_pattern(pattern.member, term.member, env, bound, hs) 
				&& fill_pattern(pattern.set, term.set, env, bound, hs);
		case "gen": {
			let n_bound = {...bound};
			n_bound[pattern.arg.name] = true;
			return fill_pattern(pattern.body, subst(term.body, term.arg, pattern.arg), env, 
				n_bound, [...hs, pattern.arg]);
		} case "not": {
			return fill_pattern(pattern.prop, term.prop, env, bound, hs);
		} case "exact": 
			return term_eq(pattern.prop, Reduce(term));
	}
}






let SK_Dlam = (arg, arg_type, body) => {
	//console.log("SK_Dlam: ", arg, arg_type, body);
	switch(body.type){
	case "deduction":
		return rules.I1(rules.A1(body.prop, arg_type), body);
	case "partial_deduction": {
		switch(body.term.type){
		case "gen": {
			let gbody = SK_Dlam(arg, arg_type, body.term.body);
			return rules.I1(rules.A5(body.prop.arg, arg_type, body.prop.body), rules.I2(body.prop.arg, gbody));
		} case "app": {
			let func = SK_Dlam(arg, arg_type, body.term.func);
			let f_arg = SK_Dlam(arg, arg_type, body.term.arg);
			return rules.I1(rules.I1(rules.A2(arg_type, f_arg.prop.right, body.prop), func), f_arg);
		} case "ref":
			if(body.term.name == arg.name)
				return thid(arg_type);
			return rules.I1(rules.A1(body.prop, arg_type), body);
		}
		break;
	}}
	
	console.log("fail: ", print_term(arg), print_term(arg_type), print_term(body), body);
	throw new Error("cannot construct sk dlam");
}

let SK_Gen = (arg, body) => {
	switch(body.type){
	case "deduction":
	case "partial_deduction": {
		return rules.I2(arg, body);
	}}
	
	return Gen(arg, body);
	//console.log(arg, body);
	//throw new Error("cannot construct sk gen");
}


let ____to_sk_memo = new Map();

let to_sk = (term, hs = {}) => {
let to_sk_ = (term, hs) => {
	//console.log("to_sk", print_term(term))
	switch(term.type){
	case "lam":
	case "not":
	case "in":
	case "arrow":
	case "match":
	case "deduction":
	case "partial_deduction":
		return term;
	case "ref":
		return hs[term.name] ?? term;
	case "ns_ref": {
		let val = ns_get(ns, term);
		if(val == null)
			throw new Error(print_term(term) + " not defined :/");
		return to_sk(val, hs);
	} case "dlam": {
		let at = to_sk(term.arg_type, hs);
		let n_hs = {...hs};
		n_hs[term.arg.name] = partial_deduction(term.arg_type, term.arg);
		return SK_Dlam(term.arg, term.arg_type, to_sk(term.body, n_hs));
	} case "gen": {
		return SK_Gen(term.arg, to_sk(term.body, hs));
	} case "rule": {
		if(term.n_args == 0)
			return rules[term.name]();
		return term;
	} case "app": {
		let func = to_sk(term.func, hs);

		switch(func.type){
		case "lam": {
			if(typeof func.arg.name != "symbol"){
				let nr = Ref(Symbol());
				return to_sk(subst(subst(func.body, func.arg, nr), nr, term.arg), hs); 
			}
			return to_sk(subst(func.body, func.arg, term.arg), hs);
		} case "deduction":
		case "partial_deduction": {
			let arg = to_sk(term.arg, hs);
			if(Reduce(func.prop).type == "gen" && arg.type == "ref")
				return rules.I1(rules.A4(func.prop, Reduce(term.arg)), func);

			//console.log("mp?", arg, print_term(Reduce(arg.prop)));
			if(Reduce(func.prop).type == "gen" && Reduce(arg.prop).type != "ref")
				return to_sk(unify_mp(func, arg), hs);
		
			return rules.I1(func, arg);
		} case "match": {
			let arg = to_sk(term.arg, hs);

			//console.log("match:");
			for(let i = 0; i < func.cases.length; i++){
				let [pattern, body] = func.cases[i];

				//console.log(print_term(pattern), "\t\t", print_term(arg));

				let env = new Map();
				if(fill_pattern(Reduce(pattern), arg.prop ?? arg, env)){
					//console.log("pattern", [pattern, arg.prop, Reduce(arg.prop)].map(print_term), env);
					let v = [...env].reduceRight((a, [x, val]) => Lam(Ref(x), a), body);
					v = [...env].reduce((a, [x, val]) => App(a, val), App(Lam(func.arg, v), arg));

					//console.log(print_term(v));
					return to_sk(v, hs);
				}
			}

			break;
		} case "rule": {
			let nr = Rule(func.name, func.fn, func.n_args, [...func.args, to_sk(term.arg, hs)]);
			if(nr.n_args == nr.args.length)
				return rules[nr.name](...nr.args);
			return nr;
		}}
		console.log("app failed :/", print_term(func), "\t", print_term(term.arg), hs);
		break;
	}}

	console.error(term);
	throw new Error("cannot deduce");
}

	if(____to_sk_memo.has(term))
		return ____to_sk_memo.get(term);

	let ret = to_sk_(term, hs);
	____to_sk_memo.set(term, ret);
	return ret;
}

	let ret = to_sk(term);
	if(dtype){
		if(term_eq(Reduce(ret.prop), Reduce(dtype))){
			return deduction(dtype, ret.proof);
		}

		throw new Error("did not match expected type");
	}

	
	return ret;	

}





