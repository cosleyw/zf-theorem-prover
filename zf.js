import {NSref, zf_parse, Ref, Rule, print_term} from "./js_src/syntax.js";
import {zf_rules, term_eq} from "./js_src/zf.js";
import {ns_get, ns_set, Ns, ns_lookup, ns_flatten} from "./js_src/ns.js"
import {deduce} from "./js_src/check2.js";
import fs from "node:fs";


let builtins = String.raw`
::__builtin__::and := \a.\b. !(a -> !b) ;

::__builtin__::loda := \p.\q. {x : !p} ::A3 q p (::A1 !p !q x) ;

::__builtin__::ldn := \x. | !!p => (::A3 p !!p) (::__builtin__::loda !p !!!p x) x; 

::__builtin__::cldn := \x. | p => (::A3 !!p p) ({x : !!!p} ::__builtin__::ldn x) x ;

::__builtin__::not_contrapose := \p. 
	| !x -> !y => ::A3 x y p ;

::__builtin__::and_intro := \f. | a => \g. | b => ({t : ::__builtin__::and a b} t) 
	(::__builtin__::not_contrapose ({ q : !!(a -> !b) } ::__builtin__::ldn q f) g);

::__builtin__::and_l := \p. | ::__builtin__::and a b 
	=> ::__builtin__::not_contrapose (({q : !a} ::__builtin__::cldn (::__builtin__::loda a !b q))) ;

::__builtin__::and_r := \p. | ::__builtin__::and a b 
	=> ::__builtin__::not_contrapose (({q : !b} ::__builtin__::cldn (::A1 !b a q)));

::__builtin__::unpack := \p1. | (::__builtin__::and A B) -> C => { p2 : A } { p3 : B } p1 (::__builtin__::and_intro p2 p3) ;

::__builtin__::ac := \p1. | A -> B => \p2. | B -> C => { p3 : A } p2 (p1 p3) ;

`;




let check_unit = (stmts, ns) => {
	let log = [];
	for(let i = 0; i < stmts.length; i++){
		let Log = (...x) => {
			console.log(x.join(" "));
			log.push([i, x.join(" ")]);
		};
		let term = stmts[i];
		if(ns_get(ns, term.name) != null){
			Log(print_term(term.name) + " already defined as", print_term(ns_get(ns, term.name)));
			return log;
		}

		switch(term.type){
			case "definition": ns_set(ns, term.name, term.def); break;
			case "derivation": {
				let ret;

				try{
					ret = deduce(ns, term.rule, term.dtype);
				}catch(e){ 
					console.log("in: " + print_term(term.name));
					throw e;
					Log(e); 
					return log; 
				}

				if(ret.type != "deduction" || ret.proof == null){
					Log("failed to derive: " + print_term(term.name));
					return log;
				}


				ns_set(ns, term.name, ret);
				if(term.dtype && false){ //TODO
					if(!term_eq(Reduce(term.dtype, ns), ret.proof.prop)){
						Log(print_term(term.name) + " doesn't prove '" 
							+ print_term(term.dtype) + "' but rather '" 
							+ print_term(ret.prop) + "'.");
						return log;
					}

					Log(print_term(term.name), print_term(term.dtype));
					ret.prop = term.dtype;
				}else{
					Log(print_term(term.name), print_term(ret.prop));
				}
			break;
			}
		}
	}

	return log;
}

let get_unit = (file) => {
	let str = fs.readFileSync(file, "utf8").split("\n")
		.map(v => v.split("--")[0]).join("\n");

	let res = zf_parse(str);
	if(res.fail)
		return null;

	return res.stack[0];
}


let check_file = (file, watch) => {
	let print_log = (log) => {
		console.clear();
		log.map(v => console.log(v[1]));
	}


	let ns = Ns();
	{
	zf_rules["_"] = (a) => Ref(Symbol(a));
	Object.entries(zf_rules).map(([name, fn]) => {
		let q = (rule) => {
			if(!rule.length)
				return rule;
			let args = Array(rule.length).fill().map((v, i) => "a" + i);
			return eval(`(${args}) => {
				let res = rule(${args}); 
				console.log(print_term(res) +  " : " + name + " " + [${args}].map(v => print_term(v)).join(" ")); 
				return res;
			}`);
		};

		ns_set(ns, NSref([name]), Rule(name, fn, fn.length ?? 0));
	});
	}

	check_unit(zf_parse(builtins).stack[0], ns); //populate builtins

	let running = false;
	let unit = get_unit(file);
	if(unit == null){
		console.log("failed to parse");
		return; 
	}
	let state = ((x) => [x, check_unit(x, ns)])(unit);
	print_log(state[1]);
	let queue = [];
	if(watch){
		fs.watchFile(file, {interval: 100, persistent: true}, ()=>{
			setTimeout(() => {
				console.log("checking...");
				queue.push(get_unit(file));
				if(running)
					return;

				running = true;
				while(queue.length){
					let unit = queue.shift();
					if(unit == null){
						console.log("failed to parse");
						continue;
					}
					let [p_unit, p_log] = state;

					let i = 0;
					for(; i < unit.length && i < p_unit.length; i++){
						if(JSON.stringify(unit[i]) != JSON.stringify(p_unit[i]))
							break;
					}

					for(let j = i; j < p_unit.length; j++)
						ns_set(ns, p_unit[j].name, null);

					let log = [...p_log.filter(v => v[0] < i), ...check_unit(unit.slice(i), ns)
						.map(v => [v[0] + i, v[1]])];


					print_log(log);
					state = [unit, log];
				}
				running = false;
			}, 100);
		});
	}
}


let print_hilbert_style_proof = (file) => {
	let ns = Ns();
	let thm_lut = {};
	let memo = {};
	let thm_num = 0;
	zf_rules["_"] = (a) => Ref(Symbol(a));
	Object.entries(zf_rules).map(([name, rule]) => {
		if(rule.length == null || rule.length == 0){
			ns_set(ns, NSref([name]), Rule(name, {type: "theorem", str:name}, 0));
			return;
		}

		let args = Array(rule.length).fill(0).map((v, i) => "a" + i);
		ns_set(ns, NSref([name]), Rule(name, eval(`(${args})=>{
			let str = "${name}" + " " + [${args}].map(v => v.type == "theorem" 
				? v.thm_num
				: "(" + print_term(v) + ")").join(" ");

			if(memo[str])
				return memo[str];

			let th = {type: "theorem", str};
			th.thm_num = thm_num++;
			thm_lut[th.thm_num] = th;
			return memo[str] = th;
		}`), rule.length));
	});

	check_unit(zf_parse(builtins).stack[0], ns); //populate builtins

	let unit = get_unit(file);
	check_unit(unit, ns);
	ns_flatten(ns).filter(v => v[1].type == "deduction" && v[1].proof.thm_num != null).map(v => {
		console.log(v[0] + " " + v[1].proof.thm_num);
	});

	Object.entries(thm_lut).map(([id, v]) => {
		console.log(id + ":", v.str);
	});

}


if(process.argv.length <= 2){
	console.log("zf [file]");
}else{
	let args = process.argv.slice(2).map(v => v.trim());

	let files = args.filter(v => v[0] != "-");
	args = args.filter(v => v[0] == "-");

	if(args.some(v => v == "--hilbert")){
		print_hilbert_style_proof(files[0]);
	}else{
		check_file(files[0], args.some(v => v == "--watch"));
	}

	//uncomment for hilbert-style proof
	//console.log(Object.entries(thm_lut).map(v => v[0] + ": " + v[1].str).join("\n"));

}
