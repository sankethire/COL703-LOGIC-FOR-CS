(* ******************************************************************************************** *)
(*                 Assignment 5: Terms, substitution, unification, resolution                   *)
(* ******************************************************************************************** *)


exception NOT_UNIFIABLE;;

(* ******************************************************************************************** *)
(*                                      Defined the Datatypes                                   *)
(* ******************************************************************************************** *)
type variable = string;;
type symbol = string;;
type term = V of variable | Node of symbol * (term list);;
type substitution = (variable * term) list;;
type signature = (symbol * int) list;;

let ispresent l ls = List.mem l ls
;;

let rec check_signaturee arity_zero syms (signaturee: signature) = match signaturee with
    [] -> (arity_zero = true)
  | (symboll, arity)::xs -> (
                              if((ispresent symboll syms) || (arity < 0)) then false
                              else if(arity = 0) then (check_signaturee true (symboll::syms) xs) else (check_signaturee (arity_zero || false) (symboll::syms) xs) 
                           )     
;;

(* ******************************************************************************************** *)
(*                                             check_sig                                        *)
(* ******************************************************************************************** *)
let check_sig (signaturee: signature) = check_signaturee false [] signaturee
;;


(* ******************************************************************************************** *)
(*                                          wfterm                                              *)
(* ******************************************************************************************** *)

let rec wfterm (signaturee: signature) termtype = match termtype with
    V(var) -> true
  | Node(symboll,[]) -> ispresent (symboll,0) signaturee
  | Node(symboll, ((x::xs) as termlist)) -> (
                                              let a = (ispresent (symboll, List.length termlist) signaturee) in
                                              match a with
                                                true -> (List.fold_left (fun boolean b -> (wfterm signaturee b && boolean)) true termlist)
                                              | false -> false
                                            )
;;

let maxi a b = if (a > b) then a else b

(* ******************************************************************************************** *)
(*                                           height ht                                          *)
(* ******************************************************************************************** *)
let rec ht termtype = match termtype with
    V(var) -> 0
  | Node(symboll,[]) -> 0
  | Node(symboll,termlist) -> 1 + (List.fold_left (fun accumulate element -> maxi (ht element) accumulate) 0 termlist) 
;;

(* ******************************************************************************************** *)
(*                                              size                                            *)
(* ******************************************************************************************** *)
let rec size termtype = match termtype with
    V(var) -> 1
  | Node(symboll,[]) -> 1
  | Node(symboll,termlist) -> 1 + (List.fold_left (fun accumulate element -> (size element) + accumulate) 0 termlist) 
;;

let rec variables_appeared l ter = match ter with
    V(var) -> var::l
  | Node(symboll,[]) -> l
  | Node(symboll,ll) -> (List.fold_left (fun l element -> (variables_appeared l element)) l ll)
;;

(* ******************************************************************************************** *)
(*                                              vars                                            *)
(* ******************************************************************************************** *)
let vars ter = variables_appeared [] ter
;;

(* ******************************************************************************************** *)
(*                                              subst                                           *)
(* ******************************************************************************************** *)
let rec subst sigma term = match term with
    V(var) -> sigma var
  | Node(symboll,[]) -> Node(symboll,[])
  | Node(symboll,termlist) -> Node(symboll, (List.map (fun element -> subst sigma element) termlist));;


let rec substitute v s t = match t with
    V(var) -> if(var = v) then s else t
  | Node(x,termlist) -> Node(x, List.map (substitute v s) termlist)
;;

let rec ifvarexists v = function
    V(var) -> (v = var)
  | Node(x,termlist) -> List.exists (ifvarexists v) termlist
;;    

let rec composition_helper (comp_s: substitution) subst1 subst2 = match(subst1,subst2) with
    ([],[]) -> comp_s
  | (x,[]) -> x @ comp_s
  | ([],y) -> y @ comp_s
  | (((var1, ter1)::xs),((var2,ter2)::ys)) -> if (ifvarexists var2 ter1) then ((var1, substitute var2 ter1 ter2)::comp_s) else (composition_helper ([(var1, ter1)] @ [(var2, ter2)] @ comp_s) xs ys)
;;

let composition_of_subst (subst1: substitution) (subst2: substitution) = composition_helper [] subst1 subst2
;;

let rec list_unify l = match l with
    [] -> []
  | (a,b):: xs -> (terms_unify a b) @ (list_unify xs)
and terms_unify term1 term2 = match (term1,term2) with
    (V(var1),V(var2)) -> if(var1=var2) then [] else [(var1,term2)]
  | (V(var),(Node(v,termlist) as ter)) -> if (not(ifvarexists var ter)) then [(var,ter)] else (raise NOT_UNIFIABLE)
  | ((Node(v,termlist) as ter),V(var)) -> if (not(ifvarexists var ter)) then [(var,ter)] else (raise NOT_UNIFIABLE)
  | (Node(a,l1), Node(b,l2)) -> if ((List.length l1 = List.length l1) && (a=b)) then (list_unify (List.combine l1 l2)) else (raise NOT_UNIFIABLE) 
;;

(* ******************************************************************************************** *)
(*                                          mgu                                                 *)
(* ******************************************************************************************** *)
let mgu term1 term2 = terms_unify term1 term2
;;


(* signatures *)

let ss1 = [("a", 0); ("f", 2); ("g", 1); ("b", 0)];;
let ss2 = [("b", -1); ("f", 2); ("g", 1)];;
let ss3 = [("d", 5); ("f", 2); ("g", 3)];;
let ss4 = [("a", 0); ("f", 2); ("g", 1); ("g", 1)];;
let ss5 = [];;

check_sig ss1;;
check_sig ss2;;
check_sig ss3;;
check_sig ss4;;
check_sig ss5;;

let t1 = V "var1";;

let t2 = Node ("z", []);;

let t3 = Node ("f", [Node ("a", []); Node ("b", [])]);;

let t4 = Node ("g", [t2]);;

let t5 = Node ("f", [Node ("a", []);
             Node ("y", [V "var2"; Node ("c", [])])]);;

let t6 = Node ("f", [Node ("a", []);
             Node ("y", [Node ("b", []);
                 Node ("c", [Node ("d", [])])])])
;;

let t7 = Node ("f", [V "var1";
             Node ("y", [V "var2";
                 Node ("c", [V "var3"])])])
;;


wfterm ss1 t1;;
wfterm ss1 t2;;
wfterm ss1 t3;;
wfterm ss1 t4;;

ht t1;;
ht t2;;
ht t3;;
ht t4;;
ht t5;;
ht t6;;
ht t7;;

size t1;;
size t2;;
size t3;;
size t4;;
size t5;;
size t6;;
size t7;;

vars t1;;
vars t2;;
vars t3;;
vars t4;;
vars t5;;
vars t6;;
vars t7;;

let tsigma v = match v with
"var1" | "var2" | "var3" | "var4" | "var5" -> Node("x",[])
| _ -> Node("y",[])
;;

subst tsigma t7;;

let s1 = [("var1", Node ("m", [])); ("var2", Node("n", [])) ];;
let s2 = [("var2", Node ("i", [])); ("var3", Node("j", [])) ];;

composition_of_subst s1 s2;;

mgu t6 t7;;
(* mgu t1 t7;; *)

let tt1 = V "x";;
let tt2 = Node("y", [tt1]);;


