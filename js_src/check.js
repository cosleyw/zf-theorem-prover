import {ns_get, ns_set, Ns, ns_lookup} from "./ns.js"
import {zf_rules, zf_ast, term_eq} from "./zf.js"
import {print_term, ZF, ZF_unit, zf_parse} from "./syntax.js";

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

const deduction = (prop, proof) => {
	if(proof == null){ throw new Error("not a proof"); }
	return {type:"deduction", prop, proof}; 
};
const partial_deduction = (prop, term) => ({type:"partial_deduction", term, prop});

let subst_barrier = (prop) => (prop.type == "barrier" ? prop : {type:"barrier", prop});

const axiom_props = {
	Z0: ZF`!\\/x.!\\/y.!y#x`,
	Z1: ZF`\\/x.\\/y.(\\/z.!((z#x->z#y)->!(z#y->z#x)))->(\\/z.!((x#z->y#z)->!(y#z->x#z)))`,
	Z2: ZF`\\/x.(!\\/a.!a#x)->(!\\/y.!!(y#x->!!(!\\/z.!!(z#y->!z#x))))`,
	Z4: ZF`\\/x. \\/y.!\\/z.!!(x#z->!y#z)`,
	Z5: ZF`\\/w. !\\/a.!\\/y.\\/x.!(x#y->!y#w)->x#a`,
	Z8: ZF`\\/x.!\\/y.!\\/z.(\\/a.a#z->a#x)->z#y`
};


let rule_type = {
	A1: (a, b) => Arrow(a, Arrow(b, a)),
	A2: (a, b, c) => Arrow(Arrow(a, Arrow(b, c)), Arrow(Arrow(a, b), Arrow(a, c))),
	A3: (a, b) => Arrow(Arrow(Not(a), Not(b)), Arrow(b, a)),
	A4: (a, v) => subst(a.body, a.arg, v),
	A5: (x, a, b) => Arrow(Gen(x, Arrow(a, b)), Arrow(a, Gen(x, b))),
	Z0: (t => () => t)(axiom_props.Z0),
	Z1: (t => () => t)(axiom_props.Z1),
	Z2: (t => () => t)(axiom_props.Z2),
	Z3: (z, x, p) => {
		let nr = Ref(Symbol());
		return exists(nr, Gen(x, iff(In(x, nr), and(In(x, z), p))));
	},
	Z4: (t => () => t)(axiom_props.Z4),
	Z5: (t => () => t)(axiom_props.Z5),
	//Z6: null,
	//Z7: null,
	Z8: (t => () => t)(axiom_props.Z8)
};



export let ns_subst = (ns, term) => {
	switch(term.type){
		case "dlam": {
			let type = ns_subst(ns, term.arg_type);
			let body = ns_subst(ns, term.body);

			if (type === term.arg_type && body === term.body) {
				return term;
			}
			
			return Dlam(term.arg, type, body);
		} case zf_ast.ND.Gen: {
			let body = ns_subst(ns, term.body);

			if(body === term.body) {
				return term;
			}

			return Gen(term.arg, body);
		} case "lam": {
			let body = ns_subst(ns, term.body);

			if(body === term.body) {
				return term;
			}

			return Lam(term.arg, body);
		} case "app": {
			let newFunc = ns_subst(ns, term.func);
			let newArg = ns_subst(ns, term.arg);

			if (newFunc === term.func && newArg === term.arg) {
				return term;
			}

			return App(newFunc, newArg);
		} case zf_ast.ND.Arrow: {
			let newLeft = ns_subst(ns, term.left);
			let newRight = ns_subst(ns, term.right);

			if (newLeft === term.left && newRight === term.right) {
				return term;
			}

			return Arrow(newLeft, newRight);
		} case zf_ast.ND.Not: {
			let newProp = ns_subst(ns, term.prop);

			if (newProp === term.prop) { 
				return term; 
			}

			return Not(newProp);
		} 
		case "match":
			return Match(term.arg, term.cases.map(([p, b]) => [ns_subst(ns, p), ns_subst(ns, b)]));
		case "exact":
			return Exact(ns_subst(ns, term.prop));
		case zf_ast.ND.Ref:
		case zf_ast.ND.In:
		case "rule":
			return term;
		case "ns_ref":
			return ns_get(ns, term);
	}

	console.log(term);
	throw new Error("failed to ns_subst");
}

let subst = (term, x, val) => {
	switch(term.type){
		case "dlam": {
			let type = subst(term.arg_type, x, val);
			if(term.arg.name != x.name){
				if(typeof term.arg.name == "symbol"){
					let body = subst(term.body, x, val);
					if(type == term.type && body === term.body) {
						return term;
					}

					return Dlam(term.arg, type, body);
				}

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
				if(typeof term.arg.name == "symbol"){
					let body = subst(term.body, x, val);
					if(body === term.body) {
						return term;
					}
					return Gen(term.arg, body);
				}

				let nr = Ref(Symbol());
				return Gen(nr, subst(subst(term.body, term.arg, nr), x, val));
			}
			return term;
		case "lam":
			if(term.arg.name != x.name){
				if(typeof term.arg.name == "symbol"){
					let body = subst(term.body, x, val);
					if(body == term.body) {
						return term;
					}
					return Lam(term.arg, body);
				}

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
					let rp = Reduce(pattern);

					//console.log("test", print_term(pattern), print_term(rp));
					let fv = pattern_fv(rp);

					let [p, b] = [...fv].reduce(([pattern, body], [name, sym]) =>
						[Reduce(subst(pattern, Ref(name), sym)), subst(body, Ref(name), sym)]
					, [rp, body]);

					return [match_exact_subst(p, x, val),
						subst(subst(b, term.arg, nr), x, val)];
				});

				return Match(nr, newCases);
			}
			return term;


		case "partial_deduction": {
			let prop = subst(term.prop, x, val);
			let c_term = subst(term.term, x, val);
			if(prop === term.prop && c_term === term.term){
				return term;
			}
			return partial_deduction(prop, c_term);
		} case "exact":
		case "rule":
		case "deduction":
		case "barrier":
			return term;
	}

	console.log(print_term(term));
	throw new Error("cannot subst");
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


let fill_pattern = (pattern, term, env, bound = {}, hs = []) => {
	if(!(pattern.type == zf_ast.ND.Ref || pattern.type == "exact") && pattern.type != term.type){
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



export let Reduce = (term, bound = {}) => {
	//console.log("reduce", print_term(term));
	switch(term.type){
		case "dlam": {
			let type = Reduce(term.arg_type, bound);
			let n_bound = Object.create(bound);
			n_bound[term.arg.name] = partial_deduction(type, term.arg);
			let body = Reduce(term.body, n_bound);
			if(body.type != "partial_deduction" && body.type != "deduction"){
				//console.log("\n\n\nbody", print_term(body));
				//console.log(body);
				throw new Error("not a deduction");
			}
			
			return partial_deduction(Arrow(type, body.prop), Dlam(term.arg, type, body.term));
		} case zf_ast.ND.Gen: {
			let body = Reduce(term.body, bound);
			if(body.type == "partial_deduction")
				return partial_deduction(Gen(term.arg, body.prop), Gen(term.arg, body.term));
			if(body.type == "deduction")
				return rules.I2(term.arg, body);
			return Gen(term.arg, body);
		} case "lam":
			return term;
		case "app": {
			let arg = Reduce(term.arg, bound);
			if(term.func.type == "dlam")
				return Reduce(subst(term.func.body, term.func.arg, subst_barrier(arg)), bound);

			let fn = Reduce(term.func, bound);
			switch(fn.type){
				case "lam":
					return Reduce(subst(fn.body, fn.arg, subst_barrier(arg)), bound);
				case "rule": {
					if(fn.args.length != fn.n_args){
						let nr = Rule(fn.name, fn.fn, fn.n_args, [...fn.args, arg]);
						if(nr.args.length == nr.n_args)
							return rules[nr.name](...nr.args);
						return nr;
					}
					break;
				} case "partial_deduction": //fallthrough
					switch(fn.prop.type){
						case zf_ast.ND.Gen:
							if(arg.type == zf_ast.ND.Ref){
								return partial_deduction(subst(fn.prop.body, fn.prop.arg, arg), App(fn.term, arg));
							}

							return Reduce(unify_mp(fn, arg), bound);
						case zf_ast.ND.Arrow:
							//TODO figure out how to make this work
							//if(fn.term.type == "dlam")
								//return Reduce(subst(fn.term.body, fn.term.arg, subst_barrier(arg)), bound);

							if(arg.type == "partial_deduction" || arg.type == "deduction"){
								return partial_deduction(fn.prop.right, 
									App(fn.term, arg.type == "partial_deduction" ? arg.term : arg));
							}
							break;
					}
				case "deduction":
					switch(fn.prop.type){
						case zf_ast.ND.Gen:
							if(arg.type == zf_ast.ND.Ref)
								return rules.I1(rules.A4(fn.prop, arg), fn);
							
							return Reduce(unify_mp(fn, arg), bound);
							break;
						case zf_ast.ND.Arrow:
							if(arg.type == "deduction")
								return rules.I1(fn, arg);
							return partial_deduction(fn.prop.right, App(fn, arg.term));
					}
					break;
				case "match":
					//console.log(print_term(term));
					//console.log("start match");
					if(arg.type == "partial_deduction" || arg.type == "deduction"){
						for(let i = 0; i < fn.cases.length; i++){
							let [pattern, body] = fn.cases[i];

							//console.log("pattern", print_term(pattern));
							//console.log("arg", print_term(arg.prop));
							let env = new Map();
							if(fill_pattern(pattern, arg.prop, env)){
								let v = [...env].reduceRight((a, [x, val]) => Lam(Ref(x), a), body);
								v = [...env].reduce((a, [x, val]) => App(a, val), App(Lam(fn.arg, v), arg));
								return Reduce(v, bound);
							}
						}

						//console.log("match failed");
					}
					break;
			}

			console.log("app failed");
			console.log("fn", fn);
			console.log("arg", arg);
			//return App(fn, arg);

			break;
		} case zf_ast.ND.Arrow:
			return Arrow(Reduce(term.left, bound), Reduce(term.right, bound));
		case zf_ast.ND.Not:
			return Not(Reduce(term.prop, bound));
		case zf_ast.ND.Ref:
			if(bound[term.name])
				return bound[term.name];
			return term;
		case zf_ast.ND.In: 
			return In(Reduce(term.member, bound), Reduce(term.set, bound));
		case "partial_deduction": 
		case "deduction":
			return term;
		case "match":
			return Match(term.arg, term.cases.map(([p, b]) => [Reduce(p), b]));
		case "exact":
			return Exact(Reduce(term.prop, bound));
		case "rule":
			if(term.args.length == term.n_args)
				return rules[term.name](...term.args);
				//return partial_deduction(rule_type[term.name](...term.args), term);
			return term;
		case "barrier":
			return term.prop;
	}

	console.log(term);
	throw new Error("cannot reduce");
};

let rules;

let SK_Dlam = (arg, arg_type, body) => {
	//console.log("SK_Dlam: ", arg, arg_type, body);
	switch(body.type){
	case "deduction":
		return rules.I1(rules.A1(body.prop, arg_type), body);
	case "partial_deduction": {
		switch(body.term.type){
		case zf_ast.ND.Gen: {
			let gbody = SK_Dlam(arg, arg_type, body.term.body);
			return rules.I1(rules.A5(body.prop.arg, arg_type, body.prop.body), rules.I2(body.prop.arg, gbody));
		} case "app": {
			let func = SK_Dlam(arg, arg_type, body.term.func);
			let f_arg = SK_Dlam(arg, arg_type, body.term.arg);
			//console.log("func/f_arg\n\t", print_term(func.prop), "\n\t", print_term(f_arg.prop));
			return rules.I1(rules.I1(rules.A2(arg_type, f_arg.prop.right, body.prop), func), f_arg);
		} case zf_ast.ND.Ref:
			if(body.term.name == arg.name)
				return thid(arg_type);
			return rules.I1(rules.A1(body.prop, arg_type), body);
		}
		break;
	}}


	console.log(body);
	console.log("fail: ", print_term(arg), "\n\n\n", print_term(arg_type), "\n\n\n",  print_term(body));
	throw new Error("cannot construct sk dlam");
}

let SK_Gen = (arg, body) => {
	switch(body.type){
	case "deduction":
	case "partial_deduction": {
		return rules.I2(arg, body);
	}}
	
	console.log(arg, body);
	throw new Error("cannot construct sk gen");
}


let thid = (a) => rules.I1(rules.I1(rules.A2(a,Arrow(a,a),a),rules.A1(a,Arrow(a,a))),rules.A1(a,a));



let to_sk = (term, hs = {}) => {
	switch(term.type){
		case zf_ast.ND.Ref:
			return hs[term.name] ?? term;
		case "dlam": {
			let n_hs = Object.create(hs);
			n_hs[term.arg.name] = partial_deduction(term.arg_type, term.arg);
			return SK_Dlam(term.arg, term.arg_type, to_sk(term.body, n_hs));
		} case zf_ast.ND.Gen: {
			return SK_Gen(term.arg, to_sk(term.body, hs));
		} case "rule":
			return rules[term.name](...term.args);
		case "app":
			let fn = to_sk(term.func, hs);
			let arg = to_sk(term.arg, hs);

			if(fn.type != "partial_deduction" && fn.type != "deduction"){
				throw new Error("not a deduction");
			}

			switch(fn.prop.type){
				case zf_ast.ND.Arrow: {
					//console.log("fn/arg\n\t", print_term(fn), "\n\t", print_term(arg));
					return rules.I1(fn, arg);
				} case zf_ast.ND.Gen:
					if(arg.type == zf_ast.ND.Ref)
						return rules.I1(rules.A4(fn.prop, arg), fn);
					return to_sk(unify_mp(fn, arg), hs);
			}

			break;
		case "partial_deduction":
		case "deduction":
			return term;
	}

	console.log(term);
	throw new Error("could not deduce");
}


export const deduce = (ns, term, dtype) => {
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

	rules = {
		I1: (a, b) => {
			let t = a.prop.right;
			if(a.type == "deduction" && b.type == "deduction"){
				//console.log("lmao\n\t", print_term(a.proof), "\n\t", print_term(b.proof));
				return deduction(t, zf_rules.I1(a.proof, b.proof));
			}
			return partial_deduction(t, App(a, b));
		},
		I2: (x, t) => {
			if(t.type == "deduction")
				return deduction(Gen(x, t.prop), zf_rules.I2(x, t.proof));
			return partial_deduction(Gen(x, t.prop), Gen(x, t));
		},
		A1: (a, b) => {
			return deduction(Arrow(a, Arrow(b, a)), 
				zf_rules.A1(a, b));
		},
		A2: (a, b, c) => {
			return deduction(Arrow(Arrow(a, Arrow(b, c)), Arrow(Arrow(a, b), Arrow(a, c))), 
				zf_rules.A2(a, b, c));
		},
		A3: (a, b) => { 
			return deduction(Arrow(Arrow(Not(a), Not(b)), Arrow(b, a)), 
				zf_rules.A3(a, b));
		},
		A4: (a, v) => {
			return deduction(Arrow(a, subst(a.body, a.arg, v)),
				zf_rules.A4(a, v));
		},
		A5: (x, a, b) => {
			return deduction(Arrow(Gen(x, Arrow(a, b)), Arrow(a, Gen(x, b))), 
				zf_rules.A5(x, a, b));
		},
		Z0: (t => () => t)(deduction(axiom_props.Z0,zf_rules.Z0)),
		Z1: (t => () => t)(deduction(axiom_props.Z1, zf_rules.Z1)),
		Z2: (t => () => t)(deduction(axiom_props.Z2, zf_rules.Z2)),
		Z3: (z, x, p) => {
			let nr = Ref(Symbol());
			return deduction(
				exists(nr, Gen(x, iff(In(x, nr), and(In(x, z), p)))),
				zf_rules.Z3(z, x, p));
		},
		Z4: (t => () => t)(deduction(axiom_props.Z4, zf_rules.Z4)),
		Z5: (t => () => t)(deduction(axiom_props.Z5, zf_rules.Z5)),
		Z6: null,
		//Z7: null,
		Z8: (t => () => t)(deduction(axiom_props.Z8, zf_rules.Z8)),
		"_": (a) => Ref(Symbol(a))
	};

	//console.log("\n\n\n\n");
	term = Reduce(ns_subst(ns, term));

	if(term.type != "deduction"){
		if(term.type != "partial_deduction")
			throw new Error("not a deduction");

		term = to_sk(term.term);
	}


	if(dtype){
		if(term_eq(term.prop, Reduce(ns_subst(ns, dtype))))
			return term;

		console.log(print_term(term.prop), print_term(Reduce(ns_subst(ns, dtype))));
		throw new Error("did not match expected type");
	}

	return term;
}


