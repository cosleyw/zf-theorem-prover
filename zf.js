import {zf_parse, Ref, Rule, print_term} from "./js_src/syntax.js";
import {zf_rules, term_eq} from "./js_src/zf.js";
import {ns_get, ns_set, Ns, ns_lookup} from "./js_src/ns.js"
import {check, Reduce} from "./js_src/check.js";
import fs from "node:fs";


let check_unit = (stmts, ns) => {

	let log = [];

	for(let i = 0; i < stmts.length; i++){
		let Log = (...x) => log.push([i, x.join(" ")]);
		let term = stmts[i];
		if(ns_get(ns, term.name) != null){
			Log(print_term(term.name) + " already defined");
			return log;
		}

		switch(term.type){
			case "definition": ns_set(ns, term.name, term.def); break;
			case "derivation": {
				let ret = check(ns, term.rule);
				if(ret.type != "ded_derivation" || ret.prop == null){
					Log("failed to derive: " + print_term(term.name));
					return log;
				}

				ns_set(ns, term.name, ret);

				if(term.name.type == "ref"){
					if(term.dtype){
						if(!term_eq(Reduce(term.dtype, ns), ret.prop.prop)){
							Log(print_term(term.name) + " doesn't prove '" 
								+ print_term(term.dtype) + "' but rather '" 
								+ print_term(ret.prop_type) + "'.");
							return log;
						}

						Log(print_term(term.name), print_term(term.dtype));
						ret.prop_type = term.dtype;
					}else{
						Log(print_term(term.name), print_term(ret.prop_type));
					}
				}
			break;
			}
		}
	}

	return log;
}

let check_file = (file, watch) => {
	let get_unit = () => {
		let str = fs.readFileSync(file, "utf8").split("\n")
			.map(v => v.split("--")[0]).join("\n");

		let res = zf_parse(str);
		if(res.fail)
			return null;

		return res.stack[0];
	}

	let print_log = (log) => log.map(v => console.log(v[1]));


	let ns = Ns();
	Object.entries(zf_rules).map(([name, fn]) => ns_set(ns, Ref(name), Rule(name, fn, [])));

	let running = false;
	let state = ((x) => [x, check_unit(x, ns)])(get_unit());
	print_log(state[1]);
	let queue = [];
	if(watch){
		fs.watchFile(file, {interval: 100, persistent: true}, ()=>{
			setTimeout(() => {
				queue.push(get_unit());
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


					console.clear();
					print_log(log);
					state = [unit, log];
				}
				running = false;
			}, 100);
		});
	}
}


if(process.argv.length <= 2){
	console.log("zf [file]");
}else{
	let args = process.argv.slice(2).map(v => v.trim());

	let files = args.filter(v => v[0] != "-");
	args = args.filter(v => v[0] == "-");

	check_file(files[0], args.some(v => v == "--watch"));
}

