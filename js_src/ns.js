
export const ns_lookup = (ns, name) => {
	let path = name.name;

	let cur = ns;
	for(let i = 0; i < path.length - 1; i++){
		let next = cur[0][path[i]];
		if(next == null){
			next = cur[0][path[i]] = [{}, {}];
		}

		cur = next;
	}

	return [cur[1], cur[1][path.at(-1)]];
}

export const ns_get = (ns, path) => ns_lookup(ns, path)[1];
export const ns_set = (ns, path, val) => ns_lookup(ns, path)[0][path.type == "ns_ref" ? path.name.at(-1) : path.name] = val;

export const Ns = () => [{}, {}];
