type prop = 
	| L of string
    | Not of prop 
    | Impl of prop * prop 
;;

type node = Node of prop list * prop;;
type hprooftree = Tree of node * hprooftree list;;

let rec element l e = match l with
	| [] -> false
	| a::l' -> if a = e then true else element l' e
;;

let axiom pr = match pr with
	| Impl(Impl(Not p1, Not q1), Impl(Impl(Not p2, q2), p3)) -> if p1 = p2 && p2 = p3 && q1 = q2 then true else false
	| Impl(Impl(p1, Impl(q1, r1)), Impl(Impl(p2, q2), Impl(p3, r2))) -> if p1 = p2 && p2 = p3 && q1 = q2 && r1 = r2 then true else false
	| Impl(p1, Impl(q, p2)) -> if p1 = p2 then true else false
	| p -> false;
;;

let rec valid_hprooftree t = match t with
	| Tree (n, l) -> (match n with
		| Node(gamma, pr) -> (match axiom pr with
			| true -> if l = [] then true else false
			| false -> (match element gamma pr with
				| true -> if l = [] then true else false
				| false -> (match l with
					| [] -> false
					| [t1; t2] -> (valid_hprooftree t1) && (valid_hprooftree t2)))))
					| l' -> false
;;

let rec map_pad l fn ps = match l with
	| e::l' -> (fn e ps) :: (map_pad l' fn ps)
	| [] -> []
;;

let rec pad t ps = match t with
	| Tree(n, l) -> (match n with
		| Node(gamma, p) -> Tree(Node(gamma @ ps, p), (map_pad l pad ps)))
;;

let rec map_used l fn = match l with
	| e::l' -> (fn e) @ (map_used l' fn)
	| [] -> []
;;

let rec used_props t = match t with
	| Tree(n, l) -> (match n with
		| Node(gamma, p) -> if element gamma p then p :: map_used l used_props else map_used l used_props)
;;

let rec map_prune l fn = match l with
	| e::l' -> (fn e) :: (map_prune l' fn)
	| [] -> []
;;

let rec prune t = let used = used_props t in (match t with
	| Tree(n, l) -> (match n with
		| Node(gamma, p) -> Tree(Node(used, p), (map_prune l prune))))
;;

let rec find_proof tl p = match tl with
	| Tree(Node(g, p'), l)::tl' -> if p' = p then Tree(Node(g, p'), l) else find_proof tl' p
;;

let rec graft pi tl = match pi with
	| Tree(Node(g, p), l) -> (match l with
		| [] -> if axiom p then pi else find_proof tl p
		| [a; b] -> Tree(Node(g, p), [(graft a tl); (graft b tl)]))
;;

let imply_tautology p g = Tree(Node(g, Impl(p, p)), [
	Tree(Node(g, Impl(Impl(p, Impl(p, p)), Impl(p, p))), [
		Tree(Node(g, Impl(Impl(p, Impl(Impl(p, p), p)), Impl(Impl(p, Impl(p, p)), Impl(p, p)))), []);
		Tree(Node(g, Impl(p, Impl(Impl(p, p), p))), [])
	]);
	Tree(Node(g, Impl(p, Impl(p, p))), [])
]);;

let rec dedthm t = match t with
	| Tree(Node(gamma, p), l) -> (match l with
		| [] -> (match gamma with
			| e::g' -> if e = p then (imply_tautology e g') else Tree(Node(g', p), []))
		| [a; Tree(Node(g'', r), l')] -> (match gamma with
			| e::g' -> Tree(Node(g', Impl(e, p)), [
				Tree(Node(g', Impl(Impl(e, r), Impl(e, p))), [
					Tree(Node(g', Impl(Impl(e, Impl(r, p)), Impl(Impl(e, r), Impl(e, p)))), []);
					dedthm a
				]);
				dedthm (Tree(Node(g'', r), l'))
			])))
;;



(* Examples *)

let proof1 = Tree(Node([], Impl(L "p", L "p")), [
	Tree(Node([], Impl(Impl(L "p", Impl(L "q", L "p")), Impl(L "p", L "p"))), [
		Tree(Node([], Impl(Impl(L "p", Impl(Impl(L "q", L "p"), L "p")), Impl(Impl(L "p", Impl(L "q", L "p")), Impl(L "p", L "p")))), []);
		Tree(Node([], Impl(L "p", Impl(Impl(L "q", L "p"), L "p"))), [])]);
	Tree(Node([], Impl(L "p", Impl(L "q", L "p"))), [])
]);;

let proof2 = Tree(Node([L "s"], Impl(L "p", L "p")), [
	Tree(Node([L "s"], Impl(Impl(L "p", Impl(L "q", L "p")), Impl(L "p", L "p"))), [
		Tree(Node([L "s"], Impl(Impl(L "p", Impl(Impl(L "q", L "p"), L "p")), Impl(Impl(L "p", Impl(L "q", L "p")), Impl(L "p", L "p")))), []);
		Tree(Node([L "s"], Impl(L "p", Impl(Impl(L "q", L "p"), L "p"))), [])]);
	Tree(Node([L "s"], Impl(L "p", Impl(L "q", L "p"))), [])
]);;

valid_hprooftree proof1;;
let padded_p1 = pad proof1 [L "s"];;
prune padded_p1;;
dedthm proof2;;

(* More Examples *)

let p1 = L "p";;
let q1 = Impl(p1, p1);;
let r1 = p1;;
let k1 = Tree(Node([], Impl(p1, Impl(q1, p1))), []);;
let s1 = Tree(Node([], Impl(Impl(p1, Impl(q1, r1)), Impl(Impl(p1, q1), Impl(p1, r1)))), []);;
let rem1 = Impl(Impl(p1, q1), Impl(p1, r1))

let h1 = Tree(Node([], rem1), [s1; k1]);;
let k2 = Tree(Node([], Impl(p1, Impl(p1, p1))), []);;
let h2 = Tree(Node([], Impl(p1, p1)), [h1; k2]);;

valid_hprooftree h1;;
valid_hprooftree h2;;

let s1 = [L "q"];;
let new_h2 = pad h2 s1;;

prune new_h2;;

let gamma = [rem1];;
let h3 = Tree(Node(gamma, Impl(p1, p1)), [Tree(Node(gamma, rem1), []); Tree(Node(gamma, Impl(p1, Impl(p1, p1))), [])]);;

let proofl = [h1];;
graft h3 proofl;;
