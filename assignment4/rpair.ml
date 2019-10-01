type prop = 
	| T
	| F
    | L of string
    | Not of prop 
    | And of prop * prop
    | Or of prop * prop
    | Impl of prop * prop 
;;

type stmnt = Stmnt of (prop list) * prop;;
(* Node types // labels are Ass, ImplI, ImplE, Int, Class, AndI, AndEL, AndER, OrIL, OrIR, OrE *)
type node = Node of string * (stmnt list) * stmnt;;
type ndprooftree = Tree of node * ndprooftree list;;

exception Normalised;;

let get_type t = match t with
	| Tree(n, l) -> (match n with
		| Node(s, stms, stm) -> s)
;;

let get_denominator t = match t with
	| Tree(n, l) -> (match n with
		| Node(s, stms, stm) -> stm)
;;

let get_prop t = match t with
	| Tree(n, l) -> (match n with
		| Node(s, stms, stm) -> (match stm with
			| Stmnt(pl, p) -> p))
;;

let rec graft ts p tl = match tl with
	| Tree (n, l) -> (match n with
		| Node (s, stms, stm) -> (match stm with
			| Stmnt (pl , p') -> if (s = "Ass" && p' = p) then ts else Tree (n, (List.map (graft ts p) l))))
;;


let rec find_rpair t = match t with
	| Tree (n, l) -> (match n with
		| Node(s, stms, stm) -> (match s with
			| "AndEL" -> if (get_type (List.hd l) = "AndI"  && get_denominator (List.hd l) = List.hd stms) then t else (
				if l != [] then List.hd (List.map find_rpair l) else raise Normalised)
			| "AndER" -> if (get_type (List.hd l) = "AndI"  && get_denominator (List.hd l) = List.hd stms) then t else (
				if l != [] then List.hd (List.map find_rpair l) else raise Normalised)
			| "OrE"   -> if ((get_type (List.hd l) = "OrIL" || get_type (List.hd l) = "OrIR") && get_denominator (List.hd l) = List.hd stms) then t else (
				if l != [] then List.hd (List.map find_rpair l) else raise Normalised)
			| "ImplE" -> if (get_type (List.hd l) = "ImplI" && get_denominator (List.hd l) = List.hd stms) then t else (
				if l != [] then List.hd (List.map find_rpair l) else raise Normalised)
			| s'      -> if l != [] then List.hd (List.map find_rpair l) else raise Normalised))
;;
