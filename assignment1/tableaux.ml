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
let rec contrad_path_ri t rho =  match t with
	| Tree (Node (L l, b), e, c, []) -> let x = lookup rho l in (
		if x = Some b then Tree (Node (L l, b), e, false, [])
		else if x = None then Tree (Node (L l, b), e, false, [])
		else Tree (Node (L l, b), e, true, []))
	| Tree (Node (L l, b), e, c, [d]) -> let x = lookup rho l in (
		if x = Some b then Tree (Node (L l, b), e, false, [contrad_path_ri d rho])
		else if x = None then Tree (Node (L l, b), e, false, [contrad_path_ri d ((l, b)::rho)])
		else Tree (Node (L l, b), e, true, [d]))
	| Tree (Node (L l, b), e, c, [d1; d2]) -> let x = lookup rho l in (
		if x = Some b then Tree (Node (L l, b), e, false, [(contrad_path_ri d1 rho); (contrad_path_ri d2 rho)])
		else if x = None then Tree (Node (L l, b), e, false, [(contrad_path_ri d1 ((l, b)::rho)); (contrad_path_ri d2 ((l, b)::rho))])
		else Tree (Node (L l, b), e, true, [d1; d2]))
	| Tree (Node (p, b), e, c, l) -> (match l with
		| [] -> Tree (Node (p, b), e, c, l)
		| [d] -> Tree (Node (p, b), e, c, [contrad_path_ri d rho])
		| [d1; d2] -> Tree (Node (p, b), e, c, [contrad_path_ri d1 rho; contrad_path_ri d2 rho]))
;;
let contrad_path t = contrad_path_ri t [];;

let rec find_assignments_ri n rho exp = match n with
	(* Beta nodes *)
	| Node (And (p1, p2), false) -> (find_assignments_ri (Node (p1, false)) rho exp) @ (find_assignments_ri (Node (p2, false)) rho exp)
	| Node (Or (p1, p2), true) -> (find_assignments_ri (Node (p1, true)) rho exp) @ (find_assignments_ri (Node (p2, true)) rho exp)
	| Node (Impl (p1, p2), true) -> (find_assignments_ri (Node (p1, false)) rho exp) @ (find_assignments_ri (Node (p2, true)) rho exp)
	| Node (Iff (p1, p2), false) -> find_assignments_ri (Node (Impl(p1, p2), false)) rho exp @ (find_assignments_ri (Node (Impl(p2, p1), false)) rho exp)
	(* Alpha nodes *)
	| Node (And (p1, p2), true) -> find_assignments_ri (Node (p1, true)) rho ((Node (p2, true))::exp)
	| Node (Or (p1, p2), false) -> find_assignments_ri (Node (p1, false)) rho ((Node (p2, false))::exp)
	| Node (Impl (p1, p2), false) -> find_assignments_ri (Node (p1, true)) rho ((Node (p2, false))::exp)
	| Node (Iff (p1, p2), true) -> find_assignments_ri (Node (Impl(p1, p2), true)) rho ((Node (Impl(p2, p1), true))::exp)
	(* Not operator *)
	| Node (Not p, b) -> find_assignments_ri (Node (p, not b)) rho exp
	(* Leaf cases, with expansion as necessary *)
	| Node (T, b) -> if (not b) then [] else (match exp with
		| (Node (p, b'))::exp' -> find_assignments_ri (Node (p, b')) rho exp'
		| [] -> [rho])
	| Node (F, b) -> if b then [] else (match exp with
		| (Node (p, b'))::exp' -> find_assignments_ri (Node (p, b')) rho exp'
		| [] -> [rho])
	| Node (L s, b) -> let x = (lookup rho s) in (
		if x = Some b then (match exp with
			| (Node (p, b'))::exp' -> find_assignments_ri (Node (p, b')) rho exp'
			| [] -> [rho])
		else if x = None then (match exp with
			| (Node (p, b'))::exp' -> find_assignments_ri (Node (p, b')) ((s, b)::rho) exp'
			| [] -> [((s, b)::rho)])
		else [])
;;
let find_assignments p b = find_assignments_ri (Node(p, b)) [] [];;

let rec step_develop_ri n rho exp = match n with
	(* Beta nodes *)
	| Node (And (p1, p2), false) -> Tree (Node (And (p1, p2), false), true, false, [(step_develop_ri (Node (p1, false)) rho exp); (step_develop_ri (Node (p2, false)) rho exp)])
	| Node (Or (p1, p2), true) -> Tree (Node (Or (p1, p2), true), true, false, [(step_develop_ri (Node (p1, true)) rho exp); (step_develop_ri (Node (p2, true)) rho exp)])
	| Node (Impl (p1, p2), true) -> Tree (Node (Impl (p1, p2), true), true, false, [(step_develop_ri (Node (p1, false)) rho exp); (step_develop_ri (Node (p2, true)) rho exp)])
	| Node (Iff (p1, p2), false) -> Tree (Node (Iff (p1, p2), false), true, false, [(step_develop_ri (Node ((Impl (p1, p2)), false)) rho exp); (step_develop_ri (Node ((Impl (p2, p1)), false)) rho exp)])
	(* Alpha nodes *)
	| Node (And (p1, p2), true) -> Tree(Node (And (p1, p2), true), true, false, [(step_develop_ri (Node (p1, true)) rho ((Node (p2, true))::exp))])
	| Node (Or (p1, p2), false) -> Tree(Node (Or (p1, p2), false), true, false, [(step_develop_ri (Node (p1, false)) rho ((Node (p2, false))::exp))])
	| Node (Impl (p1, p2), false) -> Tree(Node (Impl (p1, p2), false), true, false, [(step_develop_ri (Node (p1, true)) rho ((Node (p2, false))::exp))])
	| Node (Iff (p1, p2), true) -> Tree(Node (Iff (p1, p2), true), true, false, [(step_develop_ri (Node (Impl(p1, p2), true)) rho ((Node (Impl(p2, p1), true))::exp))])
	(* Not operator *) 
	| Node (Not p, b) -> Tree(Node (Not p, b), true, false, [(step_develop_ri (Node (p, not b)) rho exp)])
	(* Leaf cases, with expansion as necessary *)
	| Node (T, b) -> if (not b) then Tree(Node (T, b), true, true, []) else (match exp with
		| (Node (p, b'))::exp' -> Tree(Node (T, b), true, false, [(step_develop_ri (Node (p, b')) rho exp')])
		| [] -> Tree(Node (T, b), true, false, []))
	| Node (F, b) -> if b then Tree(Node (F, b), true, true, []) else (match exp with
		| (Node (p, b'))::exp' -> Tree(Node (F, b), true, false, [step_develop_ri (Node (p, b')) rho exp'])
		| [] -> Tree(Node (F, b), true, false, []))
	| Node (L s, b) -> let x = (lookup rho s) in (
		if x = Some b then (match exp with
			| (Node (p, b'))::exp' -> Tree(Node (L s, b), true, false, [step_develop_ri (Node (p, b')) rho exp'])
			| [] -> Tree(Node (L s, b), true, false, []))
		else if x = None then (match exp with
			| (Node (p, b'))::exp' -> Tree(Node (L s, b), true, false, [step_develop_ri (Node (p, b')) ((s, b)::rho) exp'])
			| [] -> Tree(Node (L s, b), true, false, []))
		else Tree(Node (L s, b), true, true, []))
;;
let step_develop n = step_develop_ri n [] [];;

let rec check_tautology p = match (find_assignments p false) with
	| [] -> true, []
	| e::l -> false, e
;;

let rec check_contradiction p = match (find_assignments p true) with
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

let rec contains l e = match l with
	| [] -> false
	| e::l' -> true
;;



(* Examples *)

let p1 = Impl(Impl(Impl(L "x1", L "x2"), L "x1"), L "x1")
let p2 = Impl(And(Impl(L "p", L "q"), Impl(L "q", L "r")), Impl(L "p", L "r"))
let p3 = Not(Or(L "p", Not(And(L "p", L "q"))))
let t1 = Or(T, L "v1")
let c1 = And(L "v2", Not(L "v2"))

let tree1 = Tree (Node (Impl (Impl (Impl (L "x1", L "x2"), L "x1"), L "x1"), false), true, false,
 [Tree (Node (Impl (Impl (L "x1", L "x2"), L "x1"), true), true, false,
   [Tree (Node (Impl (L "x1", L "x2"), false), true, false,
     [Tree (Node (L "x1", true), true, false,
       [Tree (Node (L "x2", false), true, false,
         [Tree (Node (L "x1", false), true, false, [])])])]);
    Tree (Node (L "x1", true), true, false,
     [Tree (Node (L "x1", false), true, false, [])])])])

let tree2 = Tree (Node (Impl (Impl (Impl (L "x1", L "x2"), L "x1"), L "x1"), false), true, false,
 [Tree (Node (Impl (Impl (L "x1", L "x2"), L "x1"), true), true, false,
   [Tree (Node (Impl (L "x1", L "x2"), false), true, false,
     [Tree (Node (L "x1", true), true, false,
       [Tree (Node (L "x2", false), false, false,
         [])])]);
    Tree (Node (L "x1", true), true, false,
     [Tree (Node (L "x1", false), true, false, [])])])])
;;

contrad_path tree1;;
contrad_path tree2;;
step_develop Node(p1, true);
select_node tree2;;
find_assignments p1 true;;

(* More Examples *)

let p1 = And(T, F)
let p2 = And(T, T)
let p3 = Or(T, F)
let p4 = Or(F, F)
let p5 = Impl(T, F)
let p6 = Impl(F, T)

let p7 = Or(T, L "a")
let p8 = And(F, L "b")
let p9 = Impl(F, L "c")
let p10 = Iff(T, L "d")

let p11 = Impl(p1, p2)
let p12 = Not(Iff(p3, p4))

let p13 = Iff(p10, p9)

let p14 = Not(And(p7, p8))
let p15 = Iff(Or(p7, p8), p9)
let p16 = Impl(Iff(p10, p9), p2)
let p17 = Not(And(Iff(p7, p8), Or(p8, p10)))

let p18 = And(And(Or(L "a", L "b"), And(T, L "c")), T)
;;

let t1 = check_tautology p1;;
let t2 = check_tautology p2;;
let t3 = check_tautology p3;;
let t4 = check_tautology p4;;
let t5 = check_tautology p5;;
let t6 = check_tautology p6;;
let t7 = check_tautology p7;;
let t8 = check_tautology p8;;
let t9 = check_tautology p9;;
let t10 = check_tautology p10;;
let t11 = check_tautology p11;;
let t12 = check_tautology p12;;
let t13 = check_tautology p13;;
let t14 = check_tautology p14;;
let t15 = check_tautology p15;;
let t16 = check_tautology p16;;
let t17 = check_tautology p17;;
let t18 = check_tautology p18;;
