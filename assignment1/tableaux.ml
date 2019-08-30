(* Tree and related data structures *)
type prop = 
    | T 
    | F 
    | L of string
    | Not of prop 
    | And of prop * prop 
    | Or of prop * prop 
    | Impl of prop * prop 
    | Iff of prop * prop
;;
type node = Node of prop * bool;;
(* Node, examined, lies on contradictory path, descendants *)
type tree = Tree of node * bool * bool * tree list;; 


(* Table data structure and related functions *)
type table = (string * bool) list;;
let rec lookup table k = match table with
	| [] -> None
	| (k', v)::table' -> if k'=k then Some v else lookup table' k
;;


(* Functions *)
let rec contrad_path t rho =  match t with
	| Tree (Node (L l, b), e, c, []) -> let x = lookup rho l in (
		if x = Some b then Tree (Node (L l, b), e, false, [])
		else if x = None then Tree (Node (L l, b), e, false, [])
		else Tree (Node (L l, b), e, true, []))
	| Tree (Node (L l, b), e, c, [d]) -> let x = lookup rho l in (
		if x = Some b then Tree (Node (L l, b), e, false, [contrad_path d rho])
		else if x = None then Tree (Node (L l, b), e, false, [contrad_path d ((l, b)::rho)])
		else Tree (Node (L l, b), e, true, [d]))
	| Tree (Node (L l, b), e, c, [d1; d2]) -> let x = lookup rho l in (
		if x = Some b then Tree (Node (L l, b), e, false, [(contrad_path d1 rho); (contrad_path d2 rho)])
		else if x = None then Tree (Node (L l, b), e, false, [(contrad_path d1 ((l, b)::rho)); (contrad_path d2 ((l, b)::rho))])
		else Tree (Node (L l, b), e, true, [d1; d2]))
	| t' -> t'
;;



let rec find_assignments n rho exp = match n with
	(* Beta nodes *)
	| Node (And (p1, p2), false) -> (find_assignments (Node (p1, false)) rho exp) @ (find_assignments (Node (p2, false)) rho exp)
	| Node (Or (p1, p2), true) -> (find_assignments (Node (p1, true)) rho exp) @ (find_assignments (Node (p2, true)) rho exp)
	| Node (Impl (p1, p2), true) -> (find_assignments (Node (p1, false)) rho exp) @ (find_assignments (Node (p2, true)) rho exp)
	| Node (Iff (p1, p2), false) -> find_assignments (Node (Impl(p1, p2), false)) rho ((Node (Impl(p2, p1), false))::exp)
	(* Alpha nodes *)
	| Node (And (p1, p2), true) -> find_assignments (Node (p1, true)) rho ((Node (p2, true))::exp)
	| Node (Or (p1, p2), false) -> find_assignments (Node (p1, false)) rho ((Node (p2, false))::exp)
	| Node (Impl (p1, p2), false) -> find_assignments (Node (p1, true)) rho ((Node (p2, false))::exp)
	| Node (Iff (p1, p2), true) -> find_assignments (Node (Impl(p1, p2), true)) rho ((Node (Impl(p2, p1), true))::exp)
	(* Not operator *)
	| Node (Not p, b) -> find_assignments (Node (p, not b)) rho exp
	(* Leaf cases *)
	| Node (T, b) -> if (not b) then [] else (match exp with
		| (Node (p, b))::exp' -> find_assignments (Node (p, b)) rho exp'
		| [] -> rho)
	| Node (F, b) -> if b then [] else (match exp with
		| (Node (p, b))::exp' -> find_assignments (Node (p, b)) rho exp'
		| [] -> rho)
	| Node (L s, b) -> let x = (lookup rho s) in (
		if x = Some b then (match exp with
			| (Node (p, b))::exp' -> find_assignments (Node (p, b)) rho exp'
			| [] -> rho)
		else if x = None then (match exp with
			| (Node (p, b))::exp' -> find_assignments (Node (p, b)) ((s, b)::rho) exp'
			| [] -> ((s, b)::rho))
		else [])
;;
