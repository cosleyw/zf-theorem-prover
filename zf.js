let Arrow = (left, right) => ({type: "arrow", left, right});
let Not = (prop) => ({type:"not", prop});
let Ref = (name) => ({type: "ref", name});
let Gen = (arg, body) => ({type:"gen", arg, body});
let In = (member, set) => ({type:"in", member, set});

let is_prop = (term) => {
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

let free_in = (ref, term) => {
	switch(term.type){
		case "arrow":
			return free_in(ref, term.left) || free_in(ref, term.right);
		case "not":
			return free_in(ref, term.prop);
		case "ref":
			return ref.name == term.name;
		case "gen":
			return term.arg.name != ref.name && free_in(ref, term.body);
		case "in":
			return free_in(ref, term.member) || free_in(ref, term.set);
	}
};

let symbols = 0;
let subst = (term, ref, value) => {
	switch(term.type){
		case "arrow":
			return Arrow(subst(term.left, ref, value), subst(term.right, ref, value));
		case "not":
			return Not(subst(term.prop, ref, value));
		case "ref":
			return ref.name == term.name ? value : term;
		case "gen":
			if(term.arg.name == ref.name)
				return term;

			if(free_in(term.arg, value)){
				let nr = Ref(symbols++);
				return Gen(nr, subst(subst(term.body, term.arg, nr), ref, value))
			}

			return Gen(term.arg, subst(term.body, ref, value));
		case "in":
			return In(subst(term.member, ref, value), subst(term.set, ref, value));
	}
}

let term_eq = (a, b) => {
	if(a.type != b.type)
		return false;

	switch(a.type){
		case "arrow":
			return term_eq(a.left, b.left) && term_eq(a.right, b.right);
		case "not":
			return term_eq(a.prop, b.prop);
		case "ref":
			return a.name == b.name;
		case "gen": {
			let nr = Ref(Symbol());
			return term_eq(subst(a.body, a.arg, nr), subst(b.body, b.arg, nr));
		} case "in":
			return term_eq(a.member, b.member) && term_eq(a.set, b.set);
	}
}

let Derived = (prop) => ({type: "derived", prop});
  

let I1 = (a, b) => a && b && a.type == "derived" && a.prop.type == "arrow" 
	&& b.type == "derived" && term_eq(a.prop.left, b.prop)
	? Derived(a.prop.right)
	: null;

let I2 = (ref, term) => ref && term && ref.type == "ref" && term.type == "derived"
	? Derived(Gen(ref, term.prop))
	: null;


let A1 = (a, b) => is_prop(a) && is_prop(b) 
	? Derived(Arrow(a, Arrow(b, a)))
	: null;

let A2 = (a, b, c) => is_prop(a) && is_prop(b) && is_prop(c)
	? Derived(Arrow(Arrow(a, Arrow(b, c)), Arrow(Arrow(a, b), Arrow(a, c))))
	: null;

let A3 = (a, b) => is_prop(a) && is_prop(b)
	? Derived(Arrow(Arrow(Not(a), Not(b)), Arrow(b, a)))
	: null;

let A4 = (a, v) => is_prop(a) && a.type == "gen" && v.type == "ref"
	? Derived(Arrow(a, subst(a.body, a.arg, v)))
	: null;

let A5 = (x, a, b) => x.type == "ref" && is_prop(a) && is_prop(b) && !free_in(x, a)
	? Derived(Arrow(Gen(x, Arrow(a, b)), Arrow(a, Gen(x, b))))
	: null;


let and = (a, b) => Not(Arrow(a, Not(b)));
let or = (a, b) => Arrow(Not(a), b);
let iff = (a, b) => and(Arrow(a, b), Arrow(b, a));
let exists = (x, b) => Not(Gen(x, Not(b)));
let unique = (x, b) => exists(x, and(b, Gen(y, Arrow(subst(b, x, y), Gen(z, iff(In(z, x), In(z, y)))))));


let [a, b, c, d, e, x, y, z, w] = [..."abcdexyzw"].map(Ref);

let Z0 = Derived(exists(x, Gen(y, Not(In(y, x)))));
//extensionality
let Z1 = Derived(Gen(x, Gen(y, Arrow(Gen(z, iff(In(z, x), In(z, y))), Gen(w, iff(In(x, w), In(y, w)))))));
//regularity
let Z2 = Derived(
	Gen(x, Arrow(
		exists(a, In(a, x)),
		exists(y, and(In(y, x), Not(exists(z, and(In(z, y), In(z, x))))))
	))
);
//schema of specification
let Z3 = (z, x, p) => {
	if(z && x && p && z.type == "ref" && x.type == "ref" && is_prop(p)){
		let nr = Ref(symbols++);
		return Derived(exists(nr, Gen(x, iff(In(x, nr), and(In(x, z), p)))))
	}
	return null;
};
//axiom of pairing
let Z4 = Derived(Gen(x, Gen(y, exists(z, and(In(x, z), In(y, z)))))); 
//axiom of union
let Z5 = Derived(Gen(w, exists(a, Gen(y, Gen(x, Arrow(and(In(x, y), In(y, w)), In(x, a)))))))

//axiom of replacement
let Z6 = (x, y, a, p) => {
	if(x && y && a && p && x.type == "ref" && y.type == "ref" && a.type == "ref"
	&& is_prop(p)){
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
let Z8 = Derived(Gen(x, exists(y, Gen(z, Arrow(Gen(a, Arrow(In(a, z), In(a, x))), In(z, y))))));

/*


So long as everything before here is correct it shouldn't matter how much crap i add on top


*/




let NSref = (name) => ({type: "ns_ref", name});
let Derivation = (name, dtype, rule) => ({type:"derivation", name, dtype, rule});
let Definition = (name, def) => ({type:"definition", name, def});


let Rule = (name, fn, args) => ({type: "rule", name, fn, args});
let Dlam = (arg, arg_type, body) => ({type:"dlam", arg, arg_type, body});
let Lam = (arg, body) => ({type:"lam", arg, body});
let App = (func, arg) => ({type:"app", func, arg});
let Thunk = (uneval) => uneval.type == "thunk" ? uneval : ({type:"thunk", uneval, eval:null});


let print_term = (prop, left = false, body = true) => {
	let str = "";
	switch(prop.type){
		case "arrow":
			str += print_term(prop.left, true, false) + "->" + print_term(prop.right, false, false);
			break;
		case "not":
			str += "!" + print_term(prop.prop, true, false);
			break;
		case "ref":
			return (typeof prop.name) == "number" ? "$"+prop.name.toString(36) : prop.name.toString();
		case "ns_ref":
			return prop.name.join("::");
		case "gen":
			str += "\\/" + print_term(prop.arg, false, false) + "." + print_term(prop.body, false, true);
			break;
		case "lam":
			str += "\\" + print_term(prop.arg, false, false) + "." + print_term(prop.body, false, true);
			break;
		case "in":
			return print_term(prop.member, true, false) + "#" + print_term(prop.set, true, false);
		case "derived":
			return "|-" + print_term(prop.prop);
		case "dlam":
			str += "{" + print_term(prop.arg) + " : " + print_term(prop.arg_type) 
				+ "}" + print_term(prop.body, false, true);
			break;
		case "app":
			left = !left;
			str += print_term(prop.func, true, false) + " " + print_term(prop.arg, false, false);
			break;
		case "rule":
			return prop.name;
		case "thunk":
			return term.eval ? term.eval : term.uneval;
	}

	if(left && !body)
		return "(" + str + ")";
	return str;
}


let env_lookup = (ns, name) => {
	let path;
	switch(name.type){
		case "ref":
			path = [name.name];
			break;
		case "ns_ref":
			path = name.name;
			break;
	}

	let c = ns;
	for(let i = 0; i < path.length - 1; i++){
		c = ns[0][path[i]];
		if(c == null){
			c = ns[0][path[i]] = [{}, {}];
		}
	}

	return [c[1], c[1][path.at(-1)]];
}

let Subst = (term, x, val) => {
	switch(term.type){
		case "ns_ref":
			return term;
		case "dlam": {
			let type = Subst(term.arg_type, x, val);
			if(term.arg.name != x.name){
				let nr = Ref(symbols++);
				return Dlam(nr, type, Subst(Subst(term.body, term.arg, nr), x, val));
			}
			return term;
		}case "lam":
			if(term.arg.name != x.name){
				let nr = Ref(symbols++);
				return Lam(nr, Subst(Subst(term.body, term.arg, nr), x, val));
			}
			return term;
		case "app":
			return App(Subst(term.func, x, val), Subst(term.arg, x, val));
		case "arrow":
			return Arrow(Subst(term.left, x, val), Subst(term.right, x, val));
		case "not":
			return Not(Subst(term.prop, x, val));
		case "ref":
			if(term.name == x.name)
				return val;
			return term;
		case "gen":
			if(term.arg.name != x.name){
				let nr = Ref(symbols++);
				return Gen(nr, Subst(Subst(term.body, term.arg, nr), x, val));
			}
			return term;
		case "in":
			return In(Subst(term.member, x, val), Subst(term.set, x, val));
		case "rule":
			return term;
		case "thunk":
			return term;
	}
}

let unthunk = (term) => {
	switch(term.type){
		case "ns_ref":
			return term;
		case "dlam": {
			return Dlam(term.arg, unthunk(term.arg_type), unthunk(term.body));
		}case "lam":
			return Lam(term.arg, unthunk(term.body));
		case "app":
			return App(unthunk(term.func), unthunk(term.arg));
		case "arrow":
			return Arrow(unthunk(term.left), unthunk(term.right));
		case "not":
			return Not(unthunk(term.prop));
		case "ref":
			return term;
		case "gen":
			return Gen(term.arg, unthunk(term.body));
		case "in":
			return In(unthunk(term.member), unthunk(term.set));
		case "rule":
			return term;
		case "thunk":
			return term.eval ? term.eval : term.uneval;
	}
}

let thunk_refresh = (term) => {
	switch(term.type){
		case "ns_ref":
			return term;
		case "dlam": {
			return Dlam(term.arg, unthunk(term.arg_type), unthunk(term.body));
		}case "lam":
			return Lam(term.arg, unthunk(term.body));
		case "app":
			return App(unthunk(term.func), unthunk(term.arg));
		case "arrow":
			return Arrow(unthunk(term.left), unthunk(term.right));
		case "not":
			return Not(unthunk(term.prop));
		case "ref":
			return term;
		case "gen":
			return Gen(term.arg, unthunk(term.body));
		case "in":
			return In(unthunk(term.member), unthunk(term.set));
		case "rule":
			return term;
		case "thunk":
			if(term.eval){
				term.uneval = thunk_refresh(term.eval);
				term.eval = null;
			}

			return term;
	}
}



let Reduce = (term, env, bound = {}) => {
	switch(term.type){
		case "ns_ref": {
			let [_, val] = env_lookup(env, term);
			if(val != null && val.type != "derived"){
				return val;
			}
			return term;
		} case "ref": {
			let [_, val] = env_lookup(env, term);
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
			if(func.type == "lam"){
				let nr = Ref(Symbol());
				let s1 = Subst(Subst(func.body, func.arg, nr), nr, Thunk(arg));
				return Reduce(s1, env, bound);
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
		case "thunk":
			if(term.eval){
				return term.eval;
			}

			return term.eval = Reduce(term.uneval, env, bound);
	}
}








let State = (string) => ({string, index: 0, stack: [], fail: false});
let incSt = (nxt) => (st) => {
	//console.log(st);
	let n_st = {...st};
	n_st.index++;
	return nxt(n_st);
}

let failSt = (st) => {
	let n_st = {...st};
	n_st.fail = true;
	return n_st;
}

let pushSt = (v) => (nxt) => (st) => {
	let n_st = {...st};
	n_st.stack = [...st.stack, v];
	return nxt(n_st);
}

let popSt = (fn) => (nxt) => (st) => {
	let n_st = {...st};
	n_st.stack = [...st.stack];
	return fn(n_st.stack.pop())(nxt)(n_st);
}

let Take = (chr) => (nxt) => (st) => st.string[st.index] == chr 
	? pushSt(chr)(incSt(nxt))(st)
	: failSt(st);

let Rx = (rx) => (nxt) => (st) => st.string[st.index] && rx.test(st.string[st.index])
	? pushSt(st.string[st.index])(incSt(nxt))(st)
	: failSt(st);



let Pass = (nxt) => (st) => nxt(st);

let Either = (f, g) => (nxt) => (st) => {
	let t = f(nxt)(st);
	return t.fail ? g(nxt)(st) : t;
}

let Both = (f, g) => (nxt) => f(g(nxt))

let all = (...x) => x.reduce(Both);
let some = (...x) => x.reduce(Either, (nxt) => failSt);

let Many = (f) => (nxt) => (st) => {
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

let Opt = (f) => Either(f, Pass);
let Del = all(popSt((x) => Pass));










let wspace = Opt(Both(Many(Rx(/\s/)), popSt(x => Pass)));
let identifier = Many(Rx(/[a-zA-Z0-9_]/));
let ref = all(wspace, identifier, popSt(name => pushSt(Ref(name.join("")))));
let ns_ref = all(wspace, identifier, popSt(id => pushSt(Ref(id.join("")))), 
	Opt(all(Many(all(Take(":"), Del, Take(":"), Del, 
	identifier, popSt(id => pushSt(id.join(""))))),
	popSt(mem => popSt(ns => pushSt(NSref([ns.name, ...mem]))))
)));


let zf_prop = (nxt) => {
	let expr = (nxt) => {
		let in_stmt = all(ref, wspace, Take("#"), Del, ref,
			popSt(y => popSt(x => pushSt(In(x, y)))));

		let forall = all(wspace, Take("\\"), Del, Take("/"), Del, ref, wspace, Take("."), Del, 
			expr, popSt(body => popSt(arg => pushSt(Gen(arg, body)))));

		let lambda = all(wspace, Take("\\"), Del, ref, wspace, Take("."), Del, 
			expr, popSt(body => popSt(arg => pushSt(Lam(arg, body)))));

		let match = all(wspace, Take("["), Del, expr, wspace, Take("]"), Del, 
			expr, popSt(body => popSt(arg => pushSt(Lam(arg, body)))));

		let dlam = all(
			wspace, Take("{"), Del, ref, wspace, Take(":"), Del, zf_prop,
			wspace, Take("}"), Del, expr,
			popSt(body => popSt(type => popSt(arg => 
				pushSt(Dlam(arg, type, body))))));


		let primary_expr = some(
			in_stmt, 
			ns_ref, 
			all(wspace, Take("("), Del, expr, wspace, Take(")"), Del)
		);

		let not_expr = (nxt) => some(
			primary_expr,
			forall, lambda, dlam, match,
			all(wspace, Take("!"), Del, not_expr, 
				popSt(p => pushSt(Not(p))))
		)(nxt);

		let arrow_expr = all(
			not_expr,
			Opt(all(
				Many(all(
					wspace, Take("-"), Del, Take(">"), Del,
					not_expr
				)),
				popSt(arr => popSt(st => 
					pushSt([st, ...arr].reduceRight((a, b) => Arrow(b, a)))))
			))
		);

		let app_expr = all(
				Many(arrow_expr),
				popSt(arr => pushSt(arr.length == 1 ? arr[0] : arr.reduce((a, b) => App(a, b))))
		);


		return app_expr(nxt);
	};

	return expr(nxt);
}

let ZF = (str) => all(zf_prop, wspace, Take(null))(x=>x)(State(str[0])).stack[0];

let zf_unit = (nxt) => {
	return some(all(
		Many(some(
			all(
				ns_ref,
				wspace, Take(":"), Del,
				some(
					all(
						zf_prop, wspace, Take(":"), Del,
						zf_prop,
						popSt(rule => popSt(type => popSt(name => 
							pushSt(Derivation(name, type, rule)))))
					),
					all(
						zf_prop,
						popSt(rule => popSt(name => 
							pushSt(Derivation(name, null, rule))))
					),
				),
				wspace, Take(";"), Del,
			),
			all(
				ns_ref, wspace, Take(":"), Del, Take("="), Del,
				zf_prop,
				popSt(ded => popSt(name => pushSt(Definition(name, ded)))),
				wspace, Take(";"), Del
			),
			all(
				wspace, Take("-"), Del, Take("-"), Del, Many(Rx(/[^\n]/)), Del,
				pushSt(null)
			),
			)),
			popSt(li => pushSt(li.filter(v => v)))
		), 
		all(wspace, pushSt([]))
	)(nxt);
}

















let place_holder = () => ({type:"uni_var", value: null});
let _unify = (term, target, env) => {
	if(term.type != target.type)
		return false;

	switch(term.type){
		case "ref":
			if(term_eq(term, target))
				return true;

			if(env[term.name].type == "placeholder"){
				if(env[term.name].value == null || term_eq(env[term.name].value, target)){
					env[term.name].value = target;
					return true;
				}
			}
			
			return false;
		case "gen": {
			let n_env = {...env};
			n_env[term.arg.name] = null;
			return _unify(term.body, target.body, n_env);
		} case "not":
			return _unify(term.prop, target.prop, env);
		case "arrow": 
			return _unify(term.left, target.left, env) && _unify(term.right, target.left, env);
		case "in":
			return _unify(term.member, target.member, env) && _unify(term.set, target.set, env);
	}
}

let unify = (term, target) => {
	let t_env = {};
	let assignments = [];
	while(term.type == "gen"){
		assignments.push(t_env[term.arg.name] = placeholder());
		term = term.body;
	}
	
	while(target.type == "gen"){
		t_env[target.arg.name] = null;
		target = target.body;
	}

	if(_unify(term, target, t_env))
		return uni_var;
	return null;
}



































let print_derived = false;


let zf_rules = {I1, I2, A1, A2, A3, A4, A5, Z0, Z1, Z2, Z3, Z4, Z5, Z6, /* Z7, */ Z8};

if(print_derived){
	zf_rules = Object.fromEntries(Object.entries(zf_rules).map(([name, rule]) => {
		let q = (rule) => {
			if(!rule.length)
				return rule;
			let args = Array(rule.length).fill().map((v, i) => "a" + i);
			return eval(`(${args}) => {let res = rule(${args}); console.log(print_term(res) +  " : " + name + " " + [${args}].map(v => print_term(v)).join(" ")); return res;}`);
		};


		return [name, q(rule)];
	}));
}

with(zf_rules){



let ded_thm = (hyp, thm, prf) => {
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
  
let ded_hyp = (hyp, n) => {
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
	return ded_thm(hyp, imp, hh);
}
  
let ded_thms = (h) => (fn) => (thm, mp, gen) => fn(
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


let is_indep = (term, env) => {
	switch(term.type){
		case "gen": //fall through
		case "dlam":{
			let n_env = {...env};
			n_env[term.arg.name] = null;
			return is_indep(term.body, n_env);
		} case "ref": {
			return env[term.name] == null;
		} case "ns_ref": {
			return true;
		} case "app": {
			return is_indep(term.func, env) && is_indep(term.arg, env);
		} case "rule": {
			return true;
		}
	}

	return true;
}

let deduce = (ns, term, hs, env, fns) => {
  	let dfns = [(a,b)=>b, (a, ap, b, bp)=>I1(ap, bp), (x, a, ap) => I2(x, ap)];
	if(hs.length != 0 && is_indep(term, env)){
		let [t, p] = deduce(ns, term, [], {}, dfns);
		return [t, fns[0](t, p)];
	}

	switch(term.type){
		case "dlam":{

			let n_hs = [...hs];
			n_hs.push(term.arg_type);
			let n_env = {...env};
			n_env[term.arg.name] = n_hs.length - 1;

			return ded_thms(term.arg_type)((thm, mp, gen) => {
				let [t, p] = deduce(ns, term.body, n_hs, n_env, [thm, mp, gen]);
				return [Arrow(term.arg_type, t), p];
			})(...fns);

			break;
		} case "ref": {
			if(env[term.name] != null)
				return [hs[env[term.name]], 
					ded_hyp([...hs], env[term.name])];

			let [_, val] = env_lookup(ns, term);
			if(val != null)
				return [val.prop, fns[0](val.prop, val)];

			return [Ref("not defined :/"), null];
			break;
		} case "ns_ref": {
			let [env, val] = env_lookup(ns, term);
			if(val == null || val.type != "derived")
				return [Ref("not a proof :/"), null];
			return [val.prop, fns[0](val.prop, val)];
			break;
		} case "app": {
			let func = deduce(ns, term.func, hs, env, fns);
			switch(func[0].type){
			case "arrow": {
				let arg = deduce(ns, term.arg, hs, env, fns);
				return [func[0].right, 
					fns[1](...func, ...arg)];
			break;
			} case "gen": {
				if(term.arg.type == "ref"){
					let d = A4(func[0], term.arg);
					let p = [d.prop, fns[0](d.prop, d)]

					return [p[0].right, 
						fns[1](...p, ...func)];

				}
				break;
			} case "rule": {
				let nr = Rule(func[0].name, func[0].fn, [...func[0].args, unthunk(term.arg)]);

				if(nr.fn.length == nr.args.length){
					let p = nr.fn(...nr.args);
					return [p.prop, fns[0](p.prop, p)];
				}

				return [nr, null]
			}}

			return [Ref("failed to apply :/"), null];
		} case "rule": {
			if(term.fn.length == null)
				return [term.fn.prop, fns[0](term.fn.prop, term.fn)];

			return [term, null];
		} case "gen": {
			let v = deduce(ns, term.body, hs, env, fns);
			return [Gen(term.arg, v[0]), fns[2](term.arg, ...v)]
		} case "thunk": {
			if(term.eval){
				return term.eval;
			}

			return term.eval = deduce(ns, term.uneval, hs, env, nfs);
		}
	}

	return [Ref("Not a deduction  :/"), null];
}



let print_decl = (decl) => {
	switch(decl.type){
		case "derivation": {
			let str = print_term(decl.name) + " : ";
			if(decl.dtype != null)
				str += print_term(decl.dtype) + " : ";

			return str + print_term(decl.rule);
		}case "definition":
			return print_term(decl.name) + " := " + print_term(decl.def);
	}
}




let check = (proof, rules = {}, ns, os) => {
	let ns_lookup = (path) => env_lookup(ns, path)[1];
	let ns_set = (path, val) => env_lookup(ns, path)[0][path.type == "ns_ref" ? path.name.at(-1) : path.name] = val;

	Object.entries(rules).map(([name, fn]) => ns_set(Ref(name), Rule(name, fn, [])));

	let log = [];

	for(let i = 0; i < proof.length; i++){
		let Log = (x) => log.push([i + os, x]);
		let term = proof[i];

		if(ns_lookup(term.name) != null){
			Log(`cannot redefine ${print_term(term.name)}`);
			return log;
		}

		switch(term.type){
			case "definition":
				ns_set(term.name, Reduce(term.def, ns));
			break;
			case "derivation": {
				let deriv = thunk_refresh(Reduce(term.rule, ns));
  				let fns = [(a,b)=>b, (a, ap, b, bp)=>I1(ap, bp), (x, a, ap) => I2(x, ap)];
				let val = deduce(ns, deriv, [], {}, fns)[1];


				if(val == null || val.type != "derived"){
					Log(`${print_term(term.name)} isn't a proof of anything`);
					return log;
				}

				
				if(term.dtype != null && !term_eq(val.prop, Reduce(term.dtype, ns))){
					Log(`${print_term(term.name)} doesn't prove ${print_term(term.dtype)} but rather ${print_term(val.prop)}`);
				}

				if(!print_derived && term.name.type == "ref")
					Log(
						print_term(term.name) 
						+ " " 
						+ print_term(term.dtype ?? val));

				ns_set(term.name, val);
			break;
			}
		}
	}

	return log;
}





let fs = require("fs");

let eval = (file, live) => {
	let ns = [{}, {}];
	let pp = null;
	let pl = [];
	let runs = 0;
	let running = false;
	let run = () => {
		if(runs <= 0 || running)
			return;
		while(running);
		running = true;

		let ns_lookup = (path) => env_lookup(ns, path)[1];
		let ns_set = (path, val) => env_lookup(ns, path)[0][path.type == "ns_ref" ? path.name.at(-1) : path.name] = val;

		let str = fs.readFileSync(file, {encoding: 'utf8', flag: 'r'});

		//remove comments
		str = str.split("\n").map(v => v.split("--")[0]).join("\n");

		let parse = all(zf_unit, wspace, Take(null))(x => x)(State(str))

		if(parse.fail){
			console.log("failed to parse", parse);
			running = false;
			return;
		}

		let cp = parse.stack[0];

		let np, nl = [], os = 0;

		if(pp){
			let i = 0;
			for(; i < cp.length && i < pp.length; i++){
				if(print_decl(cp[i]) != print_decl(pp[i]))
					break;
			}

			nl = pl.filter(v => v[0] < i);
			np = cp;
			cp = [...cp].slice(i);
			os = i;

			for(let j = i; j < pp.length; j++){
				ns_set(pp[j].name, null);
			}

		}else{
			np = cp;
		}


		try{
			let cl = [...nl, ...check(cp, zf_rules, 
				ns, os)];
			console.clear();
			console.log(cl.map(v => v[1]).join("\n"));
	 		[pp, pl] = [np, cl];
		}catch (e){
			console.log(e);
		}

		
		runs = Math.max(runs, 0);
		running = false;
	}


	if(live){
		fs.watchFile(file, {interval: 100, persistent: true}, ()=>{
			runs++;
			setTimeout(run, 100);
		});
	}else{
		runs++;
		run();
	}
}

if(process.argv.length <= 2){
	console.log("zf [file]");
}else{
	let args = process.argv.slice(2);

	let files = args.filter(v => v[0] != "-");
	args = args.filter(v => v[0] == "-");

	if(args.some(v => v.trim() == "--print"))
		print_derived = true;

	eval(files[0], args.some(v => v.trim() == "--watch"));
}




}
