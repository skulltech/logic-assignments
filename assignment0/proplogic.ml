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

let rec ht x = match x with
    | Not p -> 1 + ht p
    | And (p1, p2) -> 1 + max (ht p1) (ht p2)
    | Or (p1, p2) -> 1 + max (ht p1) (ht p2)
    | Impl (p1, p2) -> 1 + max (ht p1) (ht p2)
    | Iff (p1, p2) -> 1 + max (ht p1) (ht p2)
    | _ -> 0
;;

let rec size x = match x with
    | Not p -> 1 + size p
    | And (p1, p2) -> 1 + size p1 + size p2
    | Or (p1, p2) -> 1 + size p1 + size p2
    | Impl (p1, p2) -> 1 + size p1 + size p2
    | Iff (p1, p2) -> 1 + size p1 + size p2
    | _ -> 1
;;

module StringSet = Set.Make( 
  struct
    let compare = compare
    type t = string
  end)
;;

let rec letters x = match x with
    | L s -> StringSet.singleton s
    | Not p -> letters p
    | And (p1, p2) -> StringSet.union (letters p1) (letters p2)
    | Or (p1, p2) -> StringSet.union (letters p1) (letters p2)
    | Impl (p1, p2) -> StringSet.union (letters p1) (letters p2)
    | Iff (p1, p2) -> StringSet.union (letters p1) (letters p2)
    | _ -> StringSet.empty
;;


let rec subprop_if x y l s = match y with
    | p when p = x -> [s]
    | Not p -> if p = x then [s^"-1"] else subprop_if x p l (s^"-1")
    | And (p1, p2) -> (subprop_if x p1 [] (s^"0")) @ (subprop_if x p2 [] (s^"1"))
    | Or (p1, p2) -> (subprop_if x p1 [] (s^"0")) @ (subprop_if x p2 [] (s^"1"))
    | Impl (p1, p2) -> (subprop_if x p1 [] (s^"0")) @ (subprop_if x p2 [] (s^"1"))
    | Iff (p1, p2) -> (subprop_if x p1 [] (s^"0")) @ (subprop_if x p2 [] (s^"1"))
    | _ -> []

exception NotSubProp;;
let subprop_at x y = match (subprop_if x y [] "") with
    | [] -> raise NotSubProp
    | ls -> ls
;;

let rec truth x t = match x with
    | T -> true
    | F -> false
    | L s -> t s
    | Not p -> not (truth p t)
    | And (p1, p2) -> (truth p1 t) && (truth p2 t)
    | Or (p1, p2) -> (truth p1 t) || (truth p2 t)
    | Impl (p1, p2) -> (not (truth p1 t)) || (truth p2 t)
    | Iff (p1, p2) -> ((truth p1 t) && (truth p2 t)) || ((not (truth p1 t)) && (not (truth p2 t)))
;;

let rec nnf x = match x with
    | T -> T
    | F -> F
    | L s -> L s
    | Not T -> F
    | Not F -> T
    | Not (Not p) -> nnf p
    | Not And (p1, p2) -> Or (nnf (Not p1), nnf (Not p2))
    | Not Or (p1, p2) -> And (nnf (Not p1), nnf (Not p2))
    | Not p -> Not (nnf p)
    | And (p1, p2) -> And (nnf p1, nnf p2)
    | Or (p1, p2) -> And (nnf p1, nnf p2)
    | Impl (p1, p2) -> nnf (Or (Not p1, p2))
    | Iff (p1, p2) ->  nnf (Or (And (p1, p2), And (Not p1, Not p2)))
;;

let rec cnf x = match x with
    | T -> T
    | F -> F
    | L s -> L s
    | Not T -> F
    | Not F -> T
    | Not (Not p) -> cnf p
    | Not And (p1, p2) -> Or (cnf (Not p1), cnf (Not p2))
    | Not Or (p1, p2) -> And (cnf (Not p1), cnf (Not p2))
    | Not p -> Not (cnf p)
    | And (p1, p2) -> And (cnf p1, cnf p2)
    | Or (p1, And (p2, p3)) -> And (Or(cnf p1, cnf p2), Or(cnf p2, cnf p3))
    | Or (And (p2, p3), p1) -> And (Or(cnf p1, cnf p2), Or(cnf p2, cnf p3))
    | Or (p1, p2) -> Or (cnf p1, cnf p2)
    | Impl (p1, p2) -> cnf (Or (Not p1, p2))
    | Iff (p1, p2) ->  cnf (Or (And (p1, p2), And (Not p1, Not p2)))
;;

let rec dnf x = match x with
    | T -> T
    | F -> F
    | L s -> L s
    | Not T -> F
    | Not F -> T
    | Not (Not p) -> dnf p
    | Not And (p1, p2) -> Or (dnf (Not p1), dnf (Not p2))
    | Not Or (p1, p2) -> And (dnf (Not p1), dnf (Not p2))
    | Not p -> Not (dnf p)
    | Or (p1, p2) -> Or (dnf p1, dnf p2)
    | And (p1, Or (p2, p3)) -> Or (And(dnf p1, dnf p2), And(dnf p2, dnf p3))
    | And (Or (p2, p3), p1) -> Or (And(dnf p1, dnf p2), And(dnf p2, dnf p3))
    | And (p1, p2) -> And (dnf p1, dnf p2)
    | Impl (p1, p2) -> dnf (Or (Not p1, p2))
    | Iff (p1, p2) ->  dnf (Or (And (p1, p2), And (Not p1, Not p2)))
;;

let p1 = And(L "v1", Or(T, L "v2"))
let p2 = Or(T, L "v2")
let p3 = Or(F, L "v3")
let p4 = Not(And(L "v1", Not T))
let p5 = Iff(Impl(L "v1", Not T), p1)
let t1 = And(T, L "v1")
let c1 = And(L "v2", Not(L "v2"))


let table1 x = match x with
    | "v1" -> true
    | "v2" -> true
    | "v3" -> false
    | _ -> true
;;
