export const Arrow = (left, right) => ({type: "arrow", left, right});
export const Not = (prop) => ({type:"not", prop});
export const Ref = (name) => ({type: "ref", name});
export const Gen = (arg, body) => ({type:"gen", arg, body});
export const In = (member, set) => ({type:"in", member, set});

export const Rule = (name, fn, args) => ({type: "rule", name, fn, args});
export const Dlam = (arg, arg_type, body) => ({type:"dlam", arg, arg_type, body});
export const Lam = (arg, body) => ({type:"lam", arg, body});
export const Match = (arg, cases) => ({type:"match", arg, cases});
export const App = (func, arg) => ({type:"app", func, arg});

export const NSref = (name) => ({type: "ns_ref", name});
export const Derivation = (name, dtype, rule) => ({type:"derivation", name, dtype, rule});
export const Definition = (name, def) => ({type:"definition", name, def});

import {State, incSt, failSt, pushSt, popSt, Take, Rx, Pass, 
	Either, Both, all, some, Many, Opt, Del} from "./parse.js";

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
		

		let pattern = (nxt) => {
			let forall = all(wspace, Take("\\"), Del, Take("/"), Del, ref, wspace, Take("."), Del, 
				pattern, popSt(body => popSt(arg => pushSt(Gen(arg, body)))));
			
			let primary_expr = some(
				ref, 
				all(wspace, Take("("), Del, pattern, wspace, Take(")"), Del),
				all(wspace, Take("["), Del, expr, wspace, Take("]"), Del, 
					popSt(expr => pushSt({type: "exact", prop: expr})))
			);

			let not_expr = (nxt) => some(
				primary_expr,
				forall,
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

			return arrow_expr(nxt);
		}

		let match_case = all(wspace, Take("|"), Del, pattern, wspace, Take("="), Del, Take(">"), Del, expr, 
			popSt(body => popSt(match => pushSt([match, body]))));

		let match = all(wspace, Take("\\"), Del, ref, wspace, Take("."), Del, 
			Many(match_case), popSt(cases => popSt(arg => pushSt(Match(arg, cases)))));

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

export const print_term = (term) => {
	let symbols = 0;
	let sym_map = {};
	let print_ref = (v) => {
		if(typeof v.name == "symbol"){
			sym_map[v.name] ??= "✝" + (symbols++).toString(36);
			return sym_map[v.name];
		}

		return v.name;
	}

	let print_term_ = (term, left = false) => {
		let str = "";
	switch(term.type){
		case "derived":
			str += "|- " + print_term_(term.prop);
			break;
		case "ns_ref":
			return term.name.join("::");
		case "ref":
			return print_ref(term);
		case "rule":
			return term.name;
		case "dlam":
			str += "{" + print_term_(term.arg) + " : " + print_term_(term.arg_type) + "}"
				+ print_term_(term.body);
			break;
		case "lam":
			str += "\\" + print_term_(term.arg) + "." + print_term_(term.body);
			break;
		case "match":
			str += "\\" + print_term_(term.arg) + "." + 
				term.cases.map(v => "|" + print_term_(v[0]) + " => " + print_term_(v[1]))
				.join(" ");
			break;
		case "exact":
			return "[" + print_term_(term.prop) + "]";
		case "gen":
			str += "\\/" + print_term_(term.arg) + "." + print_term_(term.body);
			break;
		case "app": {
			let li = [term.arg];
			let cur = term;
			while(cur.func.type == "app"){
				li.push(cur.func.arg);
				cur = cur.func;
			}
			li.push(cur.func);

			str += li.map(v => print_term_(v, true)).reduceRight((a, b) => a + " " + b);
			break;
		} case "arrow":
			str += print_term_(term.left, true) + " -> " + print_term_(term.right);
			break;
		case "not":
			if(term.prop.type == "gen"){
				str += "!" + print_term_(term.prop);
				break;
			}

			return "!" + print_term_(term.prop, true);
		case "in":
			return print_term_(term.member) + "#" +  print_term_(term.set);
	}
		if(left)
			return "(" + str + ")";
		return str;
	}

	return print_term_(term);
}


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
			)),
			popSt(li => pushSt(li))
		), 
		all(wspace, pushSt([]))
	)(nxt);
}

export const zf_parse = (str) => all(zf_unit, wspace, Take(null))(x => x)(State(str));

