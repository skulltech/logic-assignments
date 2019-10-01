type prop = 
	| L of string
    | Not of prop 
    | Impl of prop * prop 
;;

type node = Node of prop list * prop;;
type hprooftree = Tree of node * hprooftree list;;
