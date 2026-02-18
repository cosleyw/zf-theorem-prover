import {ns_get, ns_set, Ns, ns_lookup} from "./ns.js"
import {term_eq} from "./zf.js"

let NSref = (name) => ({type: "ns_ref", name});
let Rule = (name, fn, args) => ({type: "rule", name, fn, args});
let Dlam = (arg, arg_type, body) => ({type:"dlam", arg, arg_type, body});
let Lam = (arg, body) => ({type:"lam", arg, body});
let Match = (arg, cases) => ({type:"match", arg, cases});
let App = (func, arg) => ({type:"app", func, arg});
let Arrow = (left, right) => ({type: "arrow", left, right});
let Not = (prop) => ({type:"not", prop});
let Ref = (name) => ({type: "ref", name});
let Gen = (arg, body) => ({type:"gen", arg, body});
let In = (member, set) => ({type:"in", member, set});

let match_exact_subst = (term, x, val) => {
	switch(term.type){
		case "ref":
			return term;
		case "arrow":
			return Arrow(match_exact_subst(term.left, x, val), match_exact_subst(term.right, x, val));
		case "gen": {
			let nr = Ref(Symbol());
			return term.arg.name == x.name ? term 
				: Gen(nr, match_exact_subst(subst(term.body, term.arg, nr), x, val));
		} case "not":
			return Not(match_exact_subst(term.prop, x, val));
		case "exact":
			return {type:"exact", prop: subst(term.prop, x, val)};
	}
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
		} case "gen": {
			let e1 = pattern_fv(term.body);
			delete e1.delete(term.arg.name);
			return e1;
		} case "not":
			return pattern_fv(term.prop);
		case "exact":
			return new Map();
	}
	return new Map();
}

let free_in_pattern = (x, term) => {
	switch(term.type){
		case "ref":
			return term.name == x.name;
		case "arrow":
			return free_in_pattern(x, term.left) || free_in_pattern(x, term.right);
		case "gen":
			return term.arg.name == x.name || free_in_pattern(x, term.body);
		case "not":
			return free_in_pattern(x, term.prop);
		case "exact":
			return false;
	}

	return false;
}


let fill_pattern = (pattern, term, ns, env, bound = {}, hs = []) => {
	if(!(pattern.type == "ref" || pattern.type == "exact") && pattern.type != term.type)
		return false;

	switch(pattern.type){
		case "ref": {
			if(bound[pattern.name])
				return pattern.name == term.name;

			let lam = hs.reduceRight((a, b) => Lam(b, a), term);
			if(env.get(pattern.name) == null)
				env.set(pattern.name, lam);

			let eq = (t1, t2) => {
				if(t1.type == t2.type && t1.type == "lam")
					return term_eq(t1.arg, t2.arg) && eq(t1.body, t2.body);
				return term_eq(t1, t2);
			}

			return eq(env.get(pattern.name), lam);
		} case "arrow":
			return fill_pattern(pattern.left, term.left, ns, env, bound, hs) 
				&& fill_pattern(pattern.right, term.right, ns, env, bound, hs);
		case "gen": {
			let n_bound = {...bound}; //TODO make sure this works
			n_bound[pattern.arg.name] = true;
			return fill_pattern(pattern.body, subst(term.body, term.arg, pattern.arg), ns, env, 
				n_bound, [...hs, pattern.arg]);
		} case "not": {
			return fill_pattern(pattern.prop, term.prop, ns, env, bound, hs);
		} case "exact": 
			return term_eq(Reduce(pattern.prop, ns), term);
	}
}


let subst = (term, x, val) => {
	switch(term.type){
		case "ns_ref":
			return term;
		case "dlam": {
			let type = subst(term.arg_type, x, val);
			if(term.arg.name != x.name){
				let nr = Ref(Symbol());
				return Dlam(nr, type, subst(subst(term.body, term.arg, nr), x, val));
			}
			return term;
		}case "lam":
			if(term.arg.name != x.name){
				let nr = Ref(Symbol());
				return Lam(nr, subst(subst(term.body, term.arg, nr), x, val));
			}
			return term;
		case "app":
			return App(subst(term.func, x, val), subst(term.arg, x, val));
		case "arrow":
			return Arrow(subst(term.left, x, val), subst(term.right, x, val));
		case "not":
			return Not(subst(term.prop, x, val));
		case "ref":
			if(term.name == x.name)
				return val;
			return term;
		case "gen":
			if(term.arg.name != x.name){
				let nr = Ref(Symbol());
				return Gen(nr, subst(subst(term.body, term.arg, nr), x, val));
			}
			return term;
		case "in":
			return In(subst(term.member, x, val), subst(term.set, x, val));
		case "rule":
			return term;
		case "match":
			if(term.arg.name != x.name){
				let nr = Ref(Symbol());
				return Match(nr, term.cases.map(([pattern, body]) => {
					let fv = pattern_fv(pattern);
					let [p, b] = [...fv].reduce(([pattern, body], [name, sym]) => 
						[subst(pattern, Ref(name), sym), subst(body, Ref(name), sym)]
					, [pattern, body]);

					return [match_exact_subst(match_exact_subst(p, term.arg, nr), x, val), 
						subst(subst(b, term.arg, nr), x, val)];
				}));
			}

			return term;
		case "exact":
			return term;
		case "derived":
			return term;
	}
}

export const Reduce = (term, env, bound = {}) => {
	switch(term.type){
		case "ns_ref": {
			let val = ns_get(env, term);
			if(val != null && val.type != "derived"){
				return val;
			}
			return term;
		} case "ref": {
			let val = ns_get(env, term);
			if(!bound[term.name] && val != null && val.type != "derived")
				return val;
			return term;
		} case "dlam": {
			let n_bound = {...bound};
			n_bound[term.arg.name] = true;
			return Dlam(term.arg, Reduce(term.arg_type, env, n_bound), Reduce(term.body, env, n_bound))
		} case "lam":
			return term;
		case "app":
			let func = Reduce(term.func, env, bound);
			let arg = Reduce(term.arg, env, bound);
			switch(func.type){
				case "lam":
					return Reduce(subst(func.body, func.arg, arg), env, bound);
				case "gen":
					return Reduce(subst(func.body, func.arg, arg), env, bound);
				case "arrow":
					return func.right;
				case "match":
					for(let i = 0; i < func.cases.length; i++){
						let [pattern, body] = func.cases[i];
						let p_env = new Map();
						if(fill_pattern(pattern, arg.type == "derived" ? arg.prop : arg, env, p_env)){
							let v = [...p_env].reduceRight(
								(a, [x, val]) => Lam(Ref(x), a), body);
							v = [...p_env].reduce(
								(a, [x, val]) => App(a, val), App(Lam(func.arg, v), arg));

							return Reduce(v, env);
						}
					};
					return Ref("match failed :/");
			}

			return App(func, arg);
		case "arrow":
			return Arrow(Reduce(term.left, env, bound), Reduce(term.right, env, bound));
		case "not":
			return Not(Reduce(term.prop, env, bound));
		case "gen": {
			let n_bound = {...bound};
			n_bound[term.arg.name] = true;
			return Gen(term.arg, Reduce(term.body, env, bound))
		} case "in":
			return In(Reduce(term.member, env, bound), Reduce(term.set, env, bound));
		case "rule":
			return term;
		case "match":
			return term;
		case "derived":
			return term;
	}
}



let ded_thm = (ns, hyp, thm, prf) => {
	let A1 = ns_get(ns, Ref("A1")).fn;
	let I1 = ns_get(ns, Ref("I1")).fn;

	let hh = prf;
	let imp = thm;
	while(hyp.length){
		let hl = hyp.pop();
		let p0 = A1(imp, hl);
		hh = I1(p0, hh);
		imp = Arrow(hl, imp);
	}

	return hh;
}
  
let ded_hyp = (ns, hyp, n) => {
	let A1 = ns_get(ns, Ref("A1")).fn;
	let A2 = ns_get(ns, Ref("A2")).fn;
	let I1 = ns_get(ns, Ref("I1")).fn;

	let thid = (a) => I1(I1(A2(a, Arrow(a, a), a), A1(a, Arrow(a, a))), A1(a, a));
	
	let hh = thid(hyp[n]);
	if(hyp.length == 1)
		return hh;

	let imp = hyp[n];
	while(hyp.length - 1 > n){
		let hl = hyp.pop();
		let ni = Arrow(hl, imp);

		let p0 = A2(hyp[n], imp, ni);
		let p1 = I1(A1(Arrow(imp, Arrow(hl, imp)), hyp[n]), A1(imp, hl));
		hh = I1(I1(p0, p1), hh);

		imp = ni;
	}

	imp = Arrow(hyp.pop(), imp);
	return ded_thm(ns, hyp, imp, hh);
}
  
let ded_thms = (ns, h) => (fn) => (thm, mp, gen) => {
	let A1 = ns_get(ns, Ref("A1")).fn;
	let A2 = ns_get(ns, Ref("A2")).fn;
	let A5 = ns_get(ns, Ref("A5")).fn;

	return fn(
    (a, ap) => mp(Arrow(a, Arrow(h, a)), thm(Arrow(a, Arrow(h, a)), A1(a, h)), a, thm(a, ap)),
    (a, ap, b, bp) => mp(
      Arrow(Arrow(h, a.left), Arrow(h, a.right)),
      mp(
        Arrow(Arrow(h, a), Arrow(Arrow(h, a.left), Arrow(h, a.right))),
        thm(Arrow(Arrow(h, a), Arrow(Arrow(h, a.left), Arrow(h, a.right))), A2(h, a.left, a.right)),
        Arrow(h, a),
        ap),
      Arrow(h, a.left),
      bp),
    (x, a, ap) => mp(Arrow(Gen(x, Arrow(h, a)), Arrow(h, Gen(x, a))), 
                     thm(Arrow(Gen(x, Arrow(h, a)), Arrow(h, Gen(x, a))), A5(x, h, a)), 
                     Gen(x, Arrow(h, a)), 
                     gen(x, Arrow(h, a), ap)));
}





import {print_term} from "./syntax.js";


let is_indep = (term, env) => {
	switch(term.type){
		case "gen": //fall through
		case "lam":
		case "dlam":{
			let n_env = {...env};
			n_env[term.arg.name] = null;
			return is_indep(term.body, n_env);
		} case "app": {
			return is_indep(term.func, env) && is_indep(term.arg, env);
		} case "ref": {
			return env[term.name] == null;
		} case "ns_ref": {
			return true;
		} case "app": {
			return is_indep(term.func, env) && is_indep(term.arg, env);
		} case "rule":
			return true;
	}

	return true;
}

let ded_derivation = (hyp, prop_type, prop) => ({type: "ded_derivation", hyp, prop_type, prop});
let annotate_rules = (rule, ns) => {
	let proof = rule.fn(...rule.args.map(v => Reduce(v, ns)));
	switch(rule.name){
		case "I1":
			return ded_derivation([], 
				rule.args[0].type == "arrow"
				? rule.args[0].right
				: App(rule.args[0], rule.args[1]),
				proof);
		case "I2":
			return ded_derivation([], Gen(rule.args[0], rule.args[1]), proof);
		case "A1":
			return ded_derivation([],
				Arrow(rule.args[0], Arrow(rule.args[1], rule.args[0])),
				proof);
		case "A2":
			return ded_derivation([],
				Arrow(Arrow(rule.args[0], Arrow(rule.args[1], rule.args[2])), 
					Arrow(Arrow(rule.args[0], rule.args[1]), 
						Arrow(rule.args[0], rule.args[2]))),
				proof);
		case "A3":
			return ded_derivation([],
				Arrow(Arrow(Not(rule.args[0]), Not(rule.args[1])), Arrow(rule.args[1], rule.args[0])),
				proof);
		case "A4":
			return ded_derivation([],
				Arrow(rule.args[0], 
					rule.args[1].type == "gen"
					? subst(rule.args[0].body, rule.args[0].arg, rule.args[1])
					: App(rule.args[0], rule.args[1])
				),
				proof);
		case "A5":
			return ded_derivation([],
				Arrow(Gen(rule.args[0], Arrow(rule.args[1], rule.args[2])), 
					Arrow(rule.args[1], Gen(rule.args[0], rule.args[2]))),
				proof);
		case "Z3": //TODO
		case "Z6":
	}

	return proof;
}


let deduce = (ns, term, hs, env, fns) => {
	let [d_thm, d_mp, d_gen] = fns;

	if(hs.length != 0 && is_indep(term, env)){
		let I1 = ns_get(ns, Ref("I1")).fn;
		let I2 = ns_get(ns, Ref("I2")).fn;
  		let dfns = [(a,b)=>b, (a, ap, b, bp)=>I1(ap, bp), (x, a, ap) => I2(x, ap)];

		let res = deduce(ns, term, [], {}, dfns);
		if(res.type == "ded_derivation")
			return ded_derivation([], res.prop_type, d_thm(res.prop.prop, res.prop));
		return res;
	}

	switch(term.type){
		case "derived":
			return ded_derivation([], term.prop, d_thm(term.prop, term));
		case "ded_derivation":
			return ded_derivation([], term.prop_type, d_thm(term.prop.prop, term.prop));
		case "lam":
		case "match":
			return term;
		case "dlam": {
			let n_hs = [...hs];
			n_hs.push(term.arg_type);
			let n_env = {...env};
			n_env[term.arg.name] = n_hs.length - 1;

			return ded_thms(ns, Reduce(term.arg_type, ns))((thm, mp, gen) => {
				let ret = deduce(ns, term.body, n_hs, n_env, [thm, mp, gen]);
				if(ret.type == "ded_derivation")
					return ded_derivation([], Arrow(term.arg_type, ret.prop_type), ret.prop);
				
				return Ref("Not a deduction :/");
			})(...fns);

			break;
		} case "ref": {
			if(env[term.name] != null)
				return ded_derivation([], hs[env[term.name]], 
					ded_hyp(ns, hs.map(v => Reduce(v, ns)), env[term.name]));

			let val = ns_get(ns, term);
			if(val == null)
				return Ref("not defined :/");
			return deduce(ns, val, hs, env, fns);
		} case "ns_ref": {
			let val = ns_get(ns, term);
			if(val == null)
				return Ref("not defined :/");
			return deduce(ns, val, hs, env, fns);
		} case "app": {
			let func = deduce(ns, term.func, hs, env, fns);

			switch(func.type){
			case "ded_derivation": {
				let d_func = Reduce(func.prop_type, ns);
				switch(d_func.type){
				case "arrow": {
					let arg = deduce(ns, term.arg, hs, env, fns);
					if(arg.type != "ded_derivation")
						break;

					return ded_derivation([], 
							func.prop_type.type == "arrow"
							? func.prop_type.right
							: App(func.prop_type, arg.prop_type), 
							d_mp(d_func, func.prop, 
								Reduce(arg.prop_type, ns), arg.prop)
						);
				} case "gen": {
					if(term.arg.type == "ref"){
						let A4 = ns_get(ns, Ref("A4")).fn;
						let d = A4(Reduce(func.prop_type, ns), term.arg);
						let p = [d.prop, d_thm(d.prop, d)]

						return ded_derivation([], 
							func.prop_type.type == "gen" 
							? subst(func.prop_type.body, 
								func.prop_type.arg, term.arg)
							: App(func.prop_type, term.arg), 
							d_mp(...p, d_func, func.prop));

					}
					break;
				}
				}
			break;
			} case "lam": {
				let ret = deduce(ns, 
					subst(func.body, func.arg, term.arg), 
					hs, env, fns);

				return ret;
			} case "match": {
				let arg = deduce(ns, term.arg, hs, env, fns);
				if(arg.type == "ded_derivation"){
					for(let i = 0; i < func.cases.length; i++){
						let [pattern, body] = func.cases[i];
						let p_env = new Map();
						if(fill_pattern(pattern, Reduce(arg.prop_type, ns), ns, p_env)){
							let v = [...p_env].reduceRight(
								(a, [x, val]) => Lam(Ref(x), a), body);
							v = [...p_env].reduce(
								(a, [x, val]) => App(a, val), App(Lam(func.arg, v), term.arg));
							
							return deduce(ns, v, hs, env, fns);
						}
					};
				}

				let ret = Reduce(App(func, term.arg), ns);
				return deduce(ns, ret, hs, env, fns);
				break;
			}case "rule": {
				let nr = Rule(func.name, func.fn, [...func.args, term.arg]);
				if(nr.fn.length == nr.args.length)
					return deduce(ns, annotate_rules(nr, ns), hs, env, fns);
				return nr;
			}
			}

			return Ref("failed to apply :/");
		} case "rule": {
			if(term.fn.length == null)
				return deduce(ns, term.fn, hs, env, fns);
			return term;
		} case "gen": {
			let v = deduce(ns, term.body, hs, env, fns);

			if(v.type == "ded_derivation"){
				return ded_derivation([], Gen(term.arg, v.prop_type), 
					d_gen(term.arg, Reduce(v.prop_type, ns), v.prop));
			}
			break;
		} 
	}

	return Ref("Not a deduction  :/");
};



export const check = (ns, term) => {
	let I1 = ns_get(ns, Ref("I1")).fn;
	let I2 = ns_get(ns, Ref("I2")).fn;
	let fns = [(a,b)=>b, (a, ap, b, bp)=>I1(ap, bp), (x, a, ap) => I2(x, ap)];
	return deduce(ns, term, [], {}, fns);
}
