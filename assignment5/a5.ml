type term = V of string | Node of string * (term list);;
type literal = Pos of term | Neg of term;;
exception NOT_UNIFIABLE;;


let rec uniq l = match l with
	| e::l' -> let ud = uniq l' in if List.mem e ud then ud else e::ud
	| [] -> []
;;

let check_sig signat = 	List.fold_left (fun x y -> match y with (s, a) -> x && a >= 0) true signat &&
							List.length (uniq signat) = List.length signat 
;;

let rec arity signat s = match signat with
	| (s', a)::l' -> if s' = s then a else arity l' s
	| [] -> -1
;;

let wfterm signat term = match term with
	| Node (s, l) -> List.length l = arity signat s
	| _ -> false
;;

let rec greatest l = match l with
	| [] -> 0
	| x::xs -> let tmp = greatest xs in if x > tmp then x else tmp
;;

let rec ht term = match term with
	| V var -> 0
	| Node (s, []) -> 0
	| Node (s, l) -> 1 + greatest (List.map ht l)
;;

let rec size term = match term with
	| V var -> 1
	| Node (s, l) -> 1 + (List.fold_left (fun x y -> x + y) 0 (List.map size l))
;;

let rec vars term = uniq (match term with
	| V var -> [var]
	| Node (s, []) -> []
	| Node (s, l) -> List.concat (List.map vars l))
;;

let rec subst s t = match t with
	| V var -> if Hashtbl.mem s var then Hashtbl.find s var else V var
	| Node (sm, []) -> Node (sm, [])
	| Node (sm, l) -> Node (sm, (List.map (subst s) l))
;;

let compose s1 s2 = let composed = Hashtbl.create (Hashtbl.length s1) in
                    Hashtbl.iter (fun k d -> Hashtbl.add composed k (subst s2 d)) s1;
                    Hashtbl.iter (fun k d -> Hashtbl.add composed k d) s2;
                    composed
;;

let rec mgu_ri t1 t2 sub = match t1 with
	| V v1 -> (match t2 with
		| V v2 -> if v1 <> v2 then (Hashtbl.add sub v1 t2; mgu_ri (subst sub t1) t2 sub) else sub
		| Node (s2, l2) -> Hashtbl.add sub v1 t2; mgu_ri (subst sub t1) t2 sub)
	| Node (s1, l1) -> (match t2 with
		| V v2 -> Hashtbl.add sub v2 t1; mgu_ri t1 (subst sub t2) sub
		| Node (s2, l2) -> if t1 = t2 then sub else (if s1 = s2 then
			(* List.fold_left (fun x y -> compose x (mgu_ri t1 y x)) sub l2 *)
			List.fold_left compose sub (List.map2 (fun x y -> mgu_ri x y (Hashtbl.create 0)) l1 l2) 
			else raise NOT_UNIFIABLE))
;;
let mgu t1 t2 = mgu_ri t1 t2 (Hashtbl.create 0);;

(* Testing mgu *)
let t1 = Node ("mother", [Node ("lulu", []); Node ("fifi", [])]);;
let t2 = Node ("mother", [V "x"; V "y"]);;

let rec resolvable_ri c1 c2 l = match c1 with
	| e1::c1' -> (match e1 with
		| Pos t1 -> (match c2 with
			| e2::c2' -> (match e2 with
				| Pos t2 -> resolvable_ri c1 c2' l
				| Neg t2 -> (try 
					resolvable_ri c1 c2' ((e1, e2, mgu t1 t2)::l)
					with NOT_UNIFIABLE -> resolvable_ri c1 c2' l))
			| [] -> resolvable_ri c1' c2 l)
		| Neg t1 -> (match c2 with
			| e2::c2' -> (match e2 with
				| Pos t2 -> (try 
					resolvable_ri c1 c2' ((e1, e2, mgu t1 t2)::l)
					with NOT_UNIFIABLE -> resolvable_ri c1 c2' l)
				| Neg t2 -> resolvable_ri c1 c2' l)
			| [] -> resolvable_ri c1' c2 l))
	| [] -> l
;;
let resolvable c1 c2 = resolvable_ri c1 c2 [];;

let remove l e = List.filter (fun x -> x <> e) l;;
let to_list h = Hashtbl.fold (fun k v acc -> (k, v) :: acc) h [];;
let get_mgu c1 c2 = to_list (match List.hd (resolvable c1 c2) with (l1, l2, h) -> h);;

let particular_resolution c1 c2 resolve cs = match resolve with
	| (l1, l2, htbl) -> uniq ((List.map (fun x -> (match x with
		| Pos t -> Pos (subst htbl t)
		| Neg t -> Neg (subst htbl t))) (uniq (remove c1 l1 @ remove c2 l2))) :: cs)
;;

let rec resolution_select c1 cs' cs = match cs' with
	| c2::cs'' -> (try List.hd (List.filter (fun x -> x <> cs) (List.map (fun x -> particular_resolution c1 c2 x cs) (resolvable c1 c2)))
		with Failure s -> resolution_select c1 cs'' cs)
	| [] -> []
;;

let rec resolution_selects cs' cs = match cs' with
	| c1::cs'' -> let res = resolution_select c1 cs'' cs in (match res with
		| [] -> resolution_selects cs'' cs
		| l -> l)
	| [] -> []
;;

let one_step_resolution cs = resolution_selects cs cs;;

let rec resolution cs = let cs' = one_step_resolution cs in
	if List.mem [] cs' then [] else (if cs' = [] then cs else resolution cs')
;;

(* Examples *)

let p = V "x";;
let q = V "y";;
let r = Node ("Sym1", [p; q]);;

let p1 = Pos p;;
let q1 = Pos q;;
let p2 = Neg p;;
let q2 = Neg q;;

let c1 = [p1; q1];;
let c2 = [p2; q1];;
let c3 = [p1; q2];;
let c4 = [p2; q2];;

let cs = [c1; c2; c3; c4];;

(* Example 1 *)
let c1 = [p1];;
let c2 = [q1];;
let c3 = [p2; q2];;
let cs1 = [c1; c2; c3];;

(* Example 2 *)
let a = V "a";;
let h = V "h";;
let i = V "i";;
let m = V "m";;

let a1 = Pos a;;
let a2 = Neg a;;
let h1 = Pos h;;
let h2 = Neg h;;

let i1 = Pos i;;
let i2 = Neg i;;
let m1 = Pos m;;
let m2 = Neg m;;


let c1 = [a2; h1];;
let c2 = [h2];;
let c3 = [i2; h1];;
let c4 = [m1; a1];;
let c5 = [m2; i1];;

let cs2 = [c1; c2; c3; c4; c5];;

(* Example 3 *)

let r = V "r";;
let r1 = Pos r;;
let r2 = Neg r;;

let c1 = [p1];;
let c2 = [p2; q1];;
let c3 = [p2; q2; r1];;
let c4 = [r2];;

let cs3 = [c1; c2; c3; c4];;


(* Example 4 *)
let lulu = Node ("lulu", []);;
let fifi = Node ("fifi", []);;

let t1 = Node ("mother", [lulu; fifi]);;
let x = V "x";;
let y = V "y";;

let t2 = Node ("mother", [x; y]);;
let t3 = Node ("parent", [x; y]);;

let t4 = Node ("Alive", [x]);;
let t5 = Node ("Older", [x; y]);;
let t6 = Node ("Alive", [lulu]);;
let t7 = Node ("Older", [lulu; fifi]);;

let l1 = Pos t1;;
let l2 = Neg t2;;
let l3 = Pos t3;;
let l4 = Neg t3;;
let l5 = Neg t4;;
let l6 = Pos t5;;
let l7 = Pos t6;;
let l8 = Neg t7;;

let c1 = [l1];;
let c2 = [l2; l3];;
let c3 = [l4; l5; l6];;
let c4 = [l7];;
let c5 = [l8];;

let cs4 = [c1; c2; c3; c4; c5];;
