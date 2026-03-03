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

const and = (a, b) => Not(Arrow(a, Not(b)));
const or = (a, b) => Arrow(Not(a), b);
const iff = (a, b) => and(Arrow(a, b), Arrow(b, a));
const exists = (x, b) => Not(Gen(x, Not(b)));
const unique = (x, b) => exists(x, and(b, Gen(y, Arrow(subst(b, x, y), Gen(z, iff(In(z, x), In(z, y)))))));


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
		case "match": //TODO
	}
}

let free_in_ded = (x, term) => {
	switch(term.type){
		case "gen":
		case "dlam":
			if(x.name == term.arg.name)
				return false;
			return free_in_ded(x, term.body);
		case "app":
			return free_in_ded(x, term.func) || free_in_ded(x, term.arg);
		case "ref":
			if(term.name == x.name)
				return true;
			return false;
		case "deduction":
			return false;
	}

	throw new Error("huh??");
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
	}
}




export let deduce = (ns, term) => {
	let I1 = ns_get(ns, Ref("I1")).fn;
	let I2 = ns_get(ns, Ref("I2")).fn;
	let A1 = ns_get(ns, Ref("A1")).fn;
	let A2 = ns_get(ns, Ref("A2")).fn;
	let A3 = ns_get(ns, Ref("A3")).fn;
	let A4 = ns_get(ns, Ref("A4")).fn;
	let A5 = ns_get(ns, Ref("A5")).fn;
	let Z0 = ns_get(ns, Ref("Z0")).fn;
	let Z1 = ns_get(ns, Ref("Z1")).fn;
	let Z2 = ns_get(ns, Ref("Z2")).fn;
	let Z3 = ns_get(ns, Ref("Z3")).fn;
	let Z4 = ns_get(ns, Ref("Z4")).fn;
	let Z5 = ns_get(ns, Ref("Z5")).fn;
	let Z6 = ns_get(ns, Ref("Z6")).fn;
	//let Z7 = ns_get(ns, Ref("Z7")).fn;
	let Z8 = ns_get(ns, Ref("Z8")).fn;
	
	let deduction = (prop, proof, rprop = null) => {
		/*if(proof == null){
			throw new Error("huh??");
		}

		if(!term_eq(proof.prop, Reduce(prop, ns)) || (rprop && !term_eq(proof.prop, rprop))){
			console.log("huh:\n", 
				print_term(prop), "\n",
				print_term(rprop), "\n",
				print_term(proof), "\n\n");
			throw new Error("huh?");
		}*/
		return {type:"deduction", prop, rprop: rprop ?? Reduce(prop, ns), proof};
	};
	let deduction_rules = {
		I1: (a, b) => deduction(
			a.type == "arrow"
			? a.left
			: App(a, b), 
			I1(a, b)),
		I2: (x, t) => deduction(Gen(x, t), I2(x, t)),
		A1: (a, b) => deduction(Arrow(a, Arrow(b, a)), A1(a, b)),
		A2: (a, b, c) => deduction(
			Arrow(Arrow(a, Arrow(b, c)), Arrow(Arrow(a, b), Arrow(a, c))),
			A2(a, b, c)
		),
		A3: (a, b) => deduction(
			Arrow(Arrow(Not(a), Not(b)), Arrow(b, a)),
			A3(a, b)
		),
		A4: (a, v) => deduction(
			Arrow(a, subst(a.body, a.arg, v)),
			A4(a, v)
		),
		A5: (x, a, b) => deduction(
			Arrow(Gen(x, Arrow(a, b)), Arrow(a, Gen(x, b))),
			A5(x, a, b)
		),
		Z0: () => deduction(
			ZF`!\\/x.!\\/y.!y#x`,
			Z0
		),
		Z1: () => deduction(
			ZF`\\/x.\\/y.(\\/z.!((z#x->z#y)->!(z#y->z#x)))->(\\/z.!((x#z->y#z)->!(y#z->x#z)))`,
			Z1
		),
		Z2: () => deduction(
			ZF`\\/x.(!\\/a.!a#x)->(!\\/y.!!(y#x->!!(!\\/z.!!(z#y->!z#x))))`,
			Z2
		),
		Z3: (z, x, p) => {
			let nr = Ref(Symbol());
			return deduction(
				exists(nr, Gen(x, iff(In(x, nr), and(In(x, z), p)))),
				Z3(z, x, p)
			);
		},
		Z4: () => deduction(
			ZF`\\/x. \\/y.!\\/z.!!(x#z->!y#z)`,
			Z4
		),
		Z5: () => deduction(
			ZF`\\/w. !\\/a.!\\/y.\\/x.!(x#y->!y#w)->x#a`,
			Z5
		),
		Z6: null,
		//Z7: null,
		Z8: () => deduction(
			ZF`\\/x.!\\/y.!\\/z.(\\/a.a#z->a#x)->z#y`,
			Z8
		),
	};

	let thid = (a) => I1(I1(A2(a, Arrow(a, a), a), A1(a, Arrow(a, a))), A1(a, a));

	let partial_deduction = (prop, term, rprop = null) => ({type:"partial_deduction", term, prop, rprop: rprop ?? Reduce(prop, ns)});
	let sk_deduce = (ns, term, bound = {}) => {
		switch(term?.type){
		case "lam": //fallthrough
		case "deduction":
			return term;
		case "ref":
			if(bound[term.name])
				return partial_deduction(bound[term.name][0], term, bound[term.name][1]);
		case "ns_ref": //fallthrough
			return sk_deduce(ns, ns_get(ns, term), bound);
		case "dlam": {
			let at = Reduce(term.arg_type, ns);
			if(term_eq(term.body, term.arg))
				//\x.x = S K K
				return deduction(Arrow(term.arg_type, term.arg_type), thid(at), Arrow(at, at));


			let n_bound = {...bound};
			n_bound[term.arg.name] = [term.arg_type, at];
			let sk_body = sk_deduce(ns, term.body, n_bound);

			let bt = sk_body.rprop; //Reduce(sk_body.prop, ns);

			if(sk_body.type == "deduction"){
				//\x.M = K M (!x#M)
				return deduction(
					Arrow(term.arg_type, sk_body.prop), 
					I1(A1(bt, at), sk_body.proof),
					Arrow(at, bt)
				);
			}

			let nr = Ref(Symbol());
			if(!free_in_ded(term.arg, sk_body.term)){
				//\x.M = K M (!x#M)
				return partial_deduction(
					Arrow(term.arg_type, sk_body.prop),
					App(
						deduction(
							Arrow(sk_body.prop, Arrow(term.arg_type, sk_body.prop)), 
							A1(bt, at),
							Arrow(bt, Arrow(at, bt))
						), 
						sk_body.term
					),
					Arrow(at, bt)
				);
			}

			if(sk_body.term.type == "gen"){
				let b = sk_deduce(ns, Dlam(term.arg, term.arg_type, sk_body.term.body), bound);
				let a = sk_body.term.arg;

				let bt = b.rprop; // Reduce(b.prop, ns);
				if(b.type == "deduction"){
					return deduction(
						Arrow(term.arg_type, Gen(a, b.prop.right)),
						I1(A5(a, at, bt.right), I2(a, b.proof)),
						Arrow(at, Gen(a, bt.right))
					);
				}

				return partial_deduction(
					Arrow(term.arg_type, Gen(a, b.prop.right)),
					App(
						deduction(
							Arrow(Gen(a, b.prop),
								Arrow(term.arg_type, Gen(a, b.prop.right))),
							A5(a, at, bt.right),
							Arrow(Gen(a, bt), Arrow(at, Gen(a, bt.right)))
						),
						Gen(a, b.term)
					),
					Arrow(at, Gen(a, bt.right))
				);
			}

			if(sk_body.term.type == "app"){
				//\x.M N = S (\x. M) (\x. N)
				let f = sk_deduce(ns, Dlam(term.arg, term.arg_type, sk_body.term.func), bound);	
				let a = sk_deduce(ns, Dlam(term.arg, term.arg_type, sk_body.term.arg), bound);
				let ft = f.rprop; //Reduce(f.prop, ns);
				
				if(f.type == "deduction" && a.type == "deduction"){
					return deduction(
						Arrow(term.arg_type, f.prop.right.type == "arrow" 
							? f.prop.right.right
							: App(f.prop.right, a.prop)),
						I1(
							I1(
								A2(ft.left, ft.right.left, ft.right.right),
								f.proof
							),
							a.proof
						),
						Arrow(ft.left, ft.right.right)
					);
				}

				return partial_deduction(
					Arrow(term.arg_type, f.prop.right.type == "arrow"
						? f.prop.right.right
						: App(f.prop.right, a.prop.right)),
					App(
						App(
							deduction(
								Arrow(Arrow(term.arg_type, f.prop.right), 
									Arrow(Arrow(term.arg_type, a.prop.right), 
										Arrow(term.arg_type, f.prop.right.type == "arrow" 
											? f.prop.right.right
											: App(f.prop.right, a.prop.right)))),
								A2(ft.left, ft.right.left, ft.right.right),
								Arrow(ft, 
									Arrow(Arrow(at, ft.right.left), 
										Arrow(at, ft.right.right))),
							),
							f.term ?? f
						),
						a.term ?? a
					),
					Arrow(at, ft.right.right),
				);
			}
			break;
		} case "app": {
			let f = sk_deduce(ns, term.func, bound);	

			if(f.type == "rule"){
				let nr = Rule(f.name, f.fn, f.n_args, [...f.args, Reduce(term.arg, ns)]);
				if(nr.n_args == nr.args.length)
					return deduction_rules[nr.name](...nr.args);
				return nr;
			}

			if(f.type == "lam")
				return sk_deduce(ns, Reduce(term, ns), bound);

			let ft = f.rprop; //Reduce(f.prop, ns);
			if(ft.type == "gen" && term.arg.type == "ref"){
				if(f.type == "deduction"){
					return deduction(
						f.prop.type == "gen"
						? subst(f.prop.body, f.prop.arg, term.arg)
						: App(f.prop, term.arg),
						I1(A4(ft, term.arg), f.proof),
						subst(ft.body, ft.arg, term.arg)
					);
				}

				return partial_deduction(
					App(f.prop, term.arg),
					App(
						deduction(
							Arrow(ft, 
								f.prop.type == "gen"
								? subst(f.prop.body, f.prop.arg, term.arg)
								: App(f.prop, term.arg)),
							A4(ft, term.arg),
							Arrow(ft, subst(ft.body, ft.arg, term.arg))
						),
						f.term
					),
					subst(ft.body, ft.arg, term.arg)
				);
			}

			let a = sk_deduce(ns, term.arg, bound);
			if(f.type == "deduction" && a.type == "deduction"){
				return deduction(
					f.prop.type == "arrow" 
						? f.prop.right 
						: App(f.prop, a.prop), 
					I1(f.proof, a.proof),
					ft.right
				);
			}

			return partial_deduction(
				f.prop.type == "arrow" 
					? f.prop.right 
					: App(f.prop, a.prop), 
				App(f.term ?? f, a.term ?? a),
				ft.right
			);
		} case "rule": {
			if(term.n_args == 0)
				return deduction_rules[term.name]();
			return term;
		} case "gen": {
			let b = sk_deduce(ns, term.body, bound);

			if(b.type == "deduction"){
				return deduction(
					Gen(term.arg, b.prop),
					I2(term.arg, b.proof),
					Gen(term.arg, b.rprop),
				);
			}

			return partial_deduction(Gen(term.arg, b.prop), Gen(term.arg, b.term), Gen(term.arg, b.rprop));
		}
		}

		console.log("huh:", print_term(term.term ?? term));
		throw new Error("huh?");
	}

	return sk_deduce(ns, term);
};


/*
let dummy_ns = [{}, {}];
let memo = {};
let thm_lut = {};
let thm_num = 0;
Object.entries(zf_rules).map(([name, rule]) => {

	if(rule.length == null || rule.length == 0){
		ns_set(dummy_ns, Ref(name), Rule(name, name, 0));
		return;
	}

	let args = Array(rule.length).fill(0).map((v, i) => "a" + i);
	ns_set(dummy_ns, Ref(name), Rule(name, eval(`(${args})=>{
		let str = "${name}" + "(" + [${args}].map(v => v.type == "theorem" 
			? "t" + v.thm_num
			: "ZF\`" + print_term(v) + "\`").join(",") + ")";

		if(memo[str])
			return memo[str];

		let th = {type: "theorem", str};
		th.thm_num = thm_num++;
		thm_lut[th.thm_num] = th;
		return memo[str] = th;
	}`), rule.length));
});
*/
