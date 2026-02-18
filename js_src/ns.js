
export const ns_lookup = (ns, name) => {
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

export const ns_get = (ns, path) => ns_lookup(ns, path)[1];
export const ns_set = (ns, path, val) => ns_lookup(ns, path)[0][path.type == "ns_ref" ? path.name.at(-1) : path.name] = val;

export const Ns = () => [{}, {}];
