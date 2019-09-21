(* ******************************************************************************************** *)
(*                             ASSIGNMENT 2 : Hilbert Style Proof System                        *)
(* ******************************************************************************************** *)



(* ******************************************************************************************** *)
(*                                    Defined Exception                                         *)
(* ******************************************************************************************** *)

exception EmptyList;;
exception TreeNotValid;;

(* ******************************************************************************************** *)
(*                                    Defined Proposition                                       *)
(* ******************************************************************************************** *)

type prop =   T 
            | F 
            | L of string
            | Not of prop
            | And of prop * prop
            | Or of prop * prop
            | Impl of prop * prop
            | Iff of prop * prop
;;


(* ******************************************************************************************** *)
(*                                   Defined Hibert Proof Tree                                  *)
(* ******************************************************************************************** *)

type hprooftree =   Lf of prop list * prop
                  | Mp of hprooftree * hprooftree * prop list * prop
;;

(* ******************************************************************************************** *)
(*                                          Helper Functions                                    *)
(* ******************************************************************************************** *)

(* checks if prop is in gamma as assumption *)
let isAssumption p gamma = List.mem p gamma
;;

(* checks if prop is K/S/R *)
let isKSR p = match p with
    Impl(a,Impl(b,c)) when (a = c) -> true
  | Impl(Impl(a,Impl(b,c)), Impl(Impl(d,e),Impl(f,g))) when ((a = d) && (a = f) && (b = e) && (c = g)) -> true 
  | Impl(Impl(Not(a),Not(b)), Impl(Impl(Not(c),d),e)) when ((a = c) && (a = e) && (b = d)) -> true
  | _ -> false
;;

(* ******************************************************************************************** *)
(*                                        Valid Proof Tree                                      *)
(* ******************************************************************************************** *)

let rec valid_hprooftree tree = match tree with
    Lf(gamma, p) -> if (isAssumption p gamma) then true else (isKSR p)
  | Mp(tree1,tree2,gamma,p) -> (
                                  match (tree1, tree2) with
                                      (Lf(gamma1,Impl(a,b)),Lf(gamma2,c)) when ((a = c) && (p = b)) -> ((valid_hprooftree tree1) && (valid_hprooftree tree2)) 
                                    | (Lf(gamma1,Impl(a,b)), Mp(t1,t2,gamma2,c)) when ((a = c) && (p = b)) -> ((valid_hprooftree tree1) && (valid_hprooftree tree2))  
                                    | (Mp(t1,t2,gamma1,Impl(a,b)), Lf(gamma2,c)) when ((a = c) && (p = b)) -> ((valid_hprooftree tree1) && (valid_hprooftree tree2)) 
                                    | (Mp(t1,t2,gamma1,Impl(a,b)), Mp(t3,t4,gamma2,c)) when ((a = c) && (p = b)) -> ((valid_hprooftree tree1) && (valid_hprooftree tree2)) 
                                    | _ -> false
                               )
;;

(* ******************************************************************************************** *)
(*                                           Union of lists                                     *)
(* ******************************************************************************************** *)

let make_unique xs x = if List.mem x xs then xs else x :: xs;;
let remove_duplicates xs = List.rev (List.fold_left make_unique [] xs);;
let union (a,b) = remove_duplicates (a@b);;

(* ******************************************************************************************** *)
(*                                     Pad Implementation                                       *)
(* ******************************************************************************************** *)

let rec pad pi delta = match pi with
    Lf(gamma,p) -> Lf(union(gamma,delta),p)
  | Mp(t1,t2,gamma,p) -> Mp((pad t1 delta), (pad t2 delta), (union(gamma,delta)), p)
;;

(* ******************************************************************************************** *)
(*                                    Prune Implementation                                      *)
(* ******************************************************************************************** *)

let rec tree_delta tree = match tree with
    Lf(gamma,p) -> if(isAssumption p gamma) then [p] else []
  | Mp(t1,t2,gamma,p) -> (tree_delta t1) @ (tree_delta t2)
;;

let rec prune_asper_delta tree delta = match tree with
    Lf(gamma,p) -> Lf(gamma,p)
  | Mp(t1,t2,gamma,p) -> Mp((prune_asper_delta t1 delta), (prune_asper_delta t2 delta), delta, p)
;;

let prune tree = prune_asper_delta tree (tree_delta tree)
;;

(* ******************************************************************************************** *)
(*                                       Helper Functions                                       *)
(* ******************************************************************************************** *)

let get_gamma tree = match tree with
    Lf(gamma,p) -> gamma
  | Mp(t1,t2,gamma,p) -> gamma
;;

let is_root tree p = match tree with
    Lf(gamma,a) when a = p -> true
  | Mp(t1,t2,gamma,a) when a = p -> true
  | _ -> false

let rec get_gammaTree treelist p = match treelist with
    [] -> raise EmptyList
  | l::ls -> if(is_root l p) then l else (get_gammaTree ls p);
;;

(* ******************************************************************************************** *)
(*                                        Graft Implementation                                  *)
(* ******************************************************************************************** *)

let rec graft_asper_gamma pi pilist gamma = match pi with
    Lf(gamma1,p) -> if(isAssumption p gamma1) then (get_gammaTree pilist p) else (Lf(gamma,p))
  | Mp(t1,t2,gamma1,p) -> Mp((graft_asper_gamma t1 pilist gamma), (graft_asper_gamma t2 pilist gamma), gamma, p)
;;

let rec graft pi pilist = match pilist with
    [] -> raise EmptyList
  | l::ls -> graft_asper_gamma pi pilist (get_gamma l)
;;

(* ******************************************************************************************** *)
(*                                          Helper Functions                                    *)
(* ******************************************************************************************** *)

let get_assumption tree = match tree with
    Lf(gamma,p) -> p
  | Mp(t1,t2,gamma,p) ->p
;;

let rec get_gammat p gamma_dash gamma = match gamma_dash with
    [] -> gamma
  | l::ls -> if (l = p) then (get_gammat p ls gamma) else (get_gammat p ls (l::gamma));;


(* ******************************************************************************************** *)
(*                            Deduction Theorem Implementation                                  *)
(* ******************************************************************************************** *)

let p_implies_p gamma p = let a = Impl(p,p) and b = Impl(p,Impl(L "q", p)) in
                          let c = Impl(b,a) and d = Impl(p, Impl(Impl(L "q",p),p)) in
                          let e = Impl(d,c) in
                          Mp(Mp(Lf(gamma,e),Lf(gamma,d),gamma,c), Lf(gamma,b), gamma, a)
;;

let rec deduction tree gamma p q = match tree with
    Lf(gamma1,a) when (a = p) -> p_implies_p gamma p
  | Lf(gamma1,a) when (isAssumption a gamma1) -> Mp(Lf(gamma, Impl(q,Impl(p,q))), Lf(gamma,q), gamma, Impl(p,q))
  | Lf(gamma1,a) -> if (isKSR a) then Mp(Lf(gamma, Impl(q,Impl(p,q))), Lf(gamma,q), gamma, Impl(p,q)) else (raise TreeNotValid)
  | Mp(t1,t2,gamma1,a) -> (
                            match (get_assumption t1) with
                            | Impl(b,c) when (c = q) -> let s = Impl(Impl(p,(Impl(b,q))) ,Impl(Impl(p,b), Impl(p,q))) in
                                                        let t11 = Mp(Lf(gamma, s), (deduction t1 gamma p (Impl(b,q))), gamma, Impl(Impl(p,b),Impl(p,q))) in 
                                                        Mp(t11, (deduction t2 gamma p b), gamma, Impl(p,q))
                            | _ -> raise TreeNotValid                                
                          )  
;;                                          

let dedthm tree p q = deduction tree (get_gammat p (get_gamma tree) []) p q
;;

(* ******************************************************************************************** *)
(*                                            Examples                                          *)
(* ******************************************************************************************** *)

(* let a = L "p";;
let b = L "q";;
let pa = Impl(a,b);;
let pb = Impl(a,Impl(b,a));;
let pc = Impl(pb,pa);;
let pd = Impl(a,Impl(Impl(b,a),a));;
let pe = Impl(pd,pc);;
let g = [Or(L "a", L "b"); T ;And(L"a",L "b"); a];;
let t = Mp(Mp(Lf(g,pc), Lf(g,pe), g,pd), Lf(g,pb), g, pa);;
let h = [a];;
let u = Lf(h,a);;
let v = valid_hprooftree t;;
let w = valid_hprooftree v;;
let x = dedthm u a a;; *)