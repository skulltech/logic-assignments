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
	| Tree (Node (p, b), e, c, l) -> (match l with
		| [] -> Tree (Node (p, b), e, c, l)
		| [d] -> Tree (Node (p, b), e, c, [contrad_path d rho])
		| [d1; d2] -> Tree (Node (p, b), e, c, [contrad_path d1 rho; contrad_path d2 rho]))
;;

let rec find_assignments n rho exp = match n with
	(* Beta nodes *)
	| Node (And (p1, p2), false) -> (find_assignments (Node (p1, false)) rho exp) @ (find_assignments (Node (p2, false)) rho exp)
	| Node (Or (p1, p2), true) -> (find_assignments (Node (p1, true)) rho exp) @ (find_assignments (Node (p2, true)) rho exp)
	| Node (Impl (p1, p2), true) -> (find_assignments (Node (p1, false)) rho exp) @ (find_assignments (Node (p2, true)) rho exp)
	| Node (Iff (p1, p2), false) -> find_assignments (Node (Impl(p1, p2), false)) rho exp @ (find_assignments (Node (Impl(p2, p1), false)) rho exp)
	(* Alpha nodes *)
	| Node (And (p1, p2), true) -> find_assignments (Node (p1, true)) rho ((Node (p2, true))::exp)
	| Node (Or (p1, p2), false) -> find_assignments (Node (p1, false)) rho ((Node (p2, false))::exp)
	| Node (Impl (p1, p2), false) -> find_assignments (Node (p1, true)) rho ((Node (p2, false))::exp)
	| Node (Iff (p1, p2), true) -> find_assignments (Node (Impl(p1, p2), true)) rho ((Node (Impl(p2, p1), true))::exp)
	(* Not operator *)
	| Node (Not p, b) -> find_assignments (Node (p, not b)) rho exp
	(* Leaf cases, with expansion as necessary *)
	| Node (T, b) -> if (not b) then [] else (match exp with
		| (Node (p, b'))::exp' -> find_assignments (Node (p, b')) rho exp'
		| [] -> [rho])
	| Node (F, b) -> if b then [] else (match exp with
		| (Node (p, b'))::exp' -> find_assignments (Node (p, b')) rho exp'
		| [] -> [rho])
	| Node (L s, b) -> let x = (lookup rho s) in (
		if x = Some b then (match exp with
			| (Node (p, b'))::exp' -> find_assignments (Node (p, b')) rho exp'
			| [] -> [rho])
		else if x = None then (match exp with
			| (Node (p, b'))::exp' -> find_assignments (Node (p, b')) ((s, b)::rho) exp'
			| [] -> [((s, b)::rho)])
		else [])
;;

let rec step_develop n rho exp = match n with
	(* Beta nodes *)
	| Node (And (p1, p2), false) -> Tree (Node (And (p1, p2), false), true, false, [(step_develop (Node (p1, false)) rho exp); (step_develop (Node (p2, false)) rho exp)])
	| Node (Or (p1, p2), true) -> Tree (Node (Or (p1, p2), true), true, false, [(step_develop (Node (p1, true)) rho exp); (step_develop (Node (p2, true)) rho exp)])
	| Node (Impl (p1, p2), true) -> Tree (Node (Impl (p1, p2), true), true, false, [(step_develop (Node (p1, false)) rho exp); (step_develop (Node (p2, true)) rho exp)])
	| Node (Iff (p1, p2), false) -> Tree (Node (Iff (p1, p2), false), true, false, [(step_develop (Node ((Impl (p1, p2)), false)) rho exp); (step_develop (Node ((Impl (p2, p1)), false)) rho exp)])
	(* Alpha nodes *)
	| Node (And (p1, p2), true) -> Tree(Node (And (p1, p2), true), true, false, [(step_develop (Node (p1, true)) rho ((Node (p2, true))::exp))])
	| Node (Or (p1, p2), false) -> Tree(Node (Or (p1, p2), false), true, false, [(step_develop (Node (p1, false)) rho ((Node (p2, false))::exp))])
	| Node (Impl (p1, p2), false) -> Tree(Node (Impl (p1, p2), false), true, false, [(step_develop (Node (p1, true)) rho ((Node (p2, false))::exp))])
	| Node (Iff (p1, p2), true) -> Tree(Node (Iff (p1, p2), true), true, false, [(step_develop (Node (Impl(p1, p2), true)) rho ((Node (Impl(p2, p1), true))::exp))])
	(* Not operator *) 
	| Node (Not p, b) -> Tree(Node (Not p, b), true, false, [(step_develop (Node (p, not b)) rho exp)])
	(* Leaf cases, with expansion as necessary *)
	| Node (T, b) -> if (not b) then Tree(Node (T, b), true, true, []) else (match exp with
		| (Node (p, b'))::exp' -> Tree(Node (T, b), true, false, [(step_develop (Node (p, b')) rho exp')])
		| [] -> Tree(Node (T, b), true, false, []))
	| Node (F, b) -> if b then Tree(Node (F, b), true, true, []) else (match exp with
		| (Node (p, b'))::exp' -> Tree(Node (F, b), true, false, [step_develop (Node (p, b')) rho exp'])
		| [] -> Tree(Node (F, b), true, false, []))
	| Node (L s, b) -> let x = (lookup rho s) in (
		if x = Some b then (match exp with
			| (Node (p, b'))::exp' -> Tree(Node (L s, b), true, false, [step_develop (Node (p, b')) rho exp'])
			| [] -> Tree(Node (L s, b), true, false, []))
		else if x = None then (match exp with
			| (Node (p, b'))::exp' -> Tree(Node (L s, b), true, false, [step_develop (Node (p, b')) ((s, b)::rho) exp'])
			| [] -> Tree(Node (L s, b), true, false, []))
		else Tree(Node (L s, b), true, true, []))
;;

let rec check_tautology p = match (find_assignments (Node(p, false)) [] []) with
	| [] -> true, []
	| e::l -> false, e
;;

let rec check_contradiction p = match (find_assignments (Node(p, true)) [] []) with
	| [] -> true, []
	| e::l -> false, e
;;

let rec select_node t =  match t with
	| Tree (Node (p, b), e, c, l) -> (match e with
		| false -> [Node (p, b)]
		| true -> (match l with
			| [] -> []
			| [e] -> select_node e
			| [e1; e2] -> (match ((select_node e1) @ (select_node e2)) with
				| e::l' -> [e]
				| [] -> [])))
;;

let p1 = Impl(Impl(Impl(L "x1", L "x2"), L "x1"), L "x1");;
let p2 = Impl(And(Impl(L "p", L "q"), Impl(L "q", L "r")), Impl(L "p", L "r"));;
let p3 = Not(Or(L "p", Not(And(L "p", L "q"))));;

let t1 = Tree (Node (Impl (Impl (Impl (L "x1", L "x2"), L "x1"), L "x1"), false), true, false,
 [Tree (Node (Impl (Impl (L "x1", L "x2"), L "x1"), true), true, false,
   [Tree (Node (Impl (L "x1", L "x2"), false), true, false,
     [Tree (Node (L "x1", true), true, false,
       [Tree (Node (L "x2", false), true, false,
         [Tree (Node (L "x1", false), true, false, [])])])]);
    Tree (Node (L "x1", true), true, false,
     [Tree (Node (L "x1", false), true, false, [])])])])
;;

let rec contains l e = match l with
	| [] -> false
	| e::l' -> true
;;

let t2 = Tree (Node (Impl (Impl (Impl (L "x1", L "x2"), L "x1"), L "x1"), false), true, false,
 [Tree (Node (Impl (Impl (L "x1", L "x2"), L "x1"), true), true, false,
   [Tree (Node (Impl (L "x1", L "x2"), false), true, false,
     [Tree (Node (L "x1", true), true, false,
       [Tree (Node (L "x2", false), false, false,
         [])])]);
    Tree (Node (L "x1", true), true, false,
     [Tree (Node (L "x1", false), true, false, [])])])])
;;
