

(* ******************************************************************************************** *)
(*                                         Defined Exceptions                                   *)
(* ******************************************************************************************** *)
exception DoNothing;;
exception EmptyList;;
exception TreeNotValid;;
exception TreeDNE;;
exception AlreadyNormalised;;
exception RpairNotExist;;

(* ******************************************************************************************** *)
(*                                     Defined Proposition                                      *)
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
(*                             Natural Deduction Proof Tree DS                                  *)
(* ******************************************************************************************** *)
(*                        LF  = Leaf                                                            *)
(*                        II = Imply Int (->-I)                                                 *)
(*                        IE  = Imply Elimination (->-E)                                        *)
(*                        NI = Not Int (~-Int)                                                  *)
(*                        NC = Not Class (~-Class)                                              *)
(*                        AI = And I (/\ - I)                                                   *)
(*                        AEL = And Elimination Left (/\-EL)                                    *)
(*                        AER = And Elimination Right (/\-ER)                                   *)
(*                        OIL = Or I Left (\/-IL)                                               *)
(*                        OIR = Or I Right (\/-IR)                                              *)
(*                        OE = Or Elemination (\/-E)                                            *)
(* ******************************************************************************************** *)
type ndprooftree =   LF of prop list * prop
                   | II of ndprooftree * prop list * prop
                   | IE of ndprooftree * ndprooftree * prop list * prop
                   | NI of ndprooftree * prop list * prop
                   | NC of ndprooftree * prop list * prop
                   | AI of ndprooftree * ndprooftree * prop list * prop
                   | AEL of ndprooftree * prop list * prop
                   | AER of ndprooftree * prop list * prop
                   | OIL of ndprooftree * prop list * prop
                   | OIR of ndprooftree * prop list * prop
                   | OE of ndprooftree * ndprooftree * ndprooftree * prop list * prop
;;

(* ******************************************************************************************** *)
(*                                       Helper Functions                                       *)
(* ******************************************************************************************** *)
let getroot tree = match tree with
    LF(gamma,p) -> p
  | II(t,gamma,p) -> p
  | IE(t1,t2,gamma,p) -> p
  | NI(t,gamma,p) -> p
  | NC(t,gamma,p) -> p
  | AI(t1,t2,gamma,p) -> p
  | AEL(t1,gamma,p) -> p
  | AER(t1,gamma,p) -> p
  | OIL(t1,gamma,p) -> p
  | OIR(t1,gamma,p) -> p
  | OE(t1,t2,t3,gamma,p) -> p
;; 


let getgamma tree = match tree with
    LF(gamma,p) -> gamma
  | II(t,gamma,p) -> gamma
  | IE(t1,t2,gamma,p) -> gamma
  | NI(t,gamma,p) -> gamma
  | NC(t,gamma,p) -> gamma
  | AI(t1,t2,gamma,p) -> gamma
  | AEL(t,gamma,p) -> gamma
  | AER(t,gamma,p) -> gamma
  | OIL(t,gamma,p) -> gamma
  | OIR(t,gamma,p) -> gamma
  | OE(t1,t2,t3,gamma,p) -> gamma
;;

let rec delete_el p l = match l with
    [] -> []
  | x::xs -> if x=p then (delete_el p xs) else (x::(delete_el p xs))
;;

let rec listequal (l1,l2) = match (l1,l2) with 
    ([],[]) -> true
  | ([],x::xs) -> false
  | (x::xs,[]) -> false
  | (x::xs, y::ys) -> listequal ((delete_el x l1) , (delete_el x l2))
;;

(* ******************************************************************************************** *)
(*                                           Union of lists                                     *)
(* ******************************************************************************************** *)

let make_unique xs x = if List.mem x xs then xs else x :: xs;;
let remove_duplicates xs = List.rev (List.fold_left make_unique [] xs);;
let union (a,b) = remove_duplicates (a@b);;

(* ******************************************************************************************** *)
(*                                        Valid ND-Proof Tree                                   *)
(* ******************************************************************************************** *)
let rec valid_ndprooftree tree = match tree with
    LF(gamma, T) -> true
  | LF(gamma, p) -> if (List.mem p gamma) then true else false
  | II(t,gamma,p) -> (
                        match p with
                         Impl(a,b) when (b = getroot t) && (listequal(getgamma t , union(gamma,[a]))) -> valid_ndprooftree t
                         | _ -> false
                     )
  | IE(t1,t2,gamma,p) -> (
                            let r1 = getroot t1 and r2 = getroot t2 in
                            match (r1,r2) with
                              (Impl(a,b),c) when (a=c) && (b=p) && (listequal(getgamma t1 , getgamma t2)) -> (valid_ndprooftree t1) &&  (valid_ndprooftree t2)
                            | _ -> false
                         )
  | NI(t,gamma,p) -> if ((getroot t = F) && (listequal(getgamma t , gamma))) then (valid_ndprooftree t) else false
  | NC(t,gamma,p) -> if ((getroot t = F) && (listequal(getgamma t , gamma@[Not(p)]))) then (valid_ndprooftree t) else false
  | AI(t1,t2,gamma,p) -> (
                            match p with
                              And(a,b) -> if ((getroot t1 = a) && (getroot t2 = b) && (listequal(getgamma t1 , gamma)) && (listequal(getgamma t2 , gamma))) then (valid_ndprooftree t1) &&  (valid_ndprooftree t2) else false
                            | _ -> false
                         )
  | AEL(t,gamma,p) -> (
                        let r = getroot t in
                        match r with
                          And(a,b) -> if ((p=a) && (listequal(getgamma t , gamma))) then (valid_ndprooftree t) else false
                        | _ -> false
                      )
  | AER(t,gamma,p) -> (
                        let r = getroot t in
                        match r with
                          And(a,b) -> if ((p=b) && (listequal(getgamma t , gamma))) then (valid_ndprooftree t) else false
                        | _ -> false 
                      )
  | OIL(t,gamma,p) -> (
                        match p with
                          Or(a,b) -> if((getroot t = a) && (listequal(getgamma t , gamma))) then (valid_ndprooftree t) else false
                        | _ -> false 
                      )
  | OIR(t,gamma,p) -> (
                        match p with
                          Or(a,b) -> if ((getroot t = b) && (listequal(getgamma t , gamma))) then (valid_ndprooftree t) else false
                        | _ -> false
                      )
  | OE(t1,t2,t3,gamma,p) -> (
                              let r1 = getroot t1 in
                              match r1 with
                                Or(a,b) -> if ((getroot t2 = p) && (getroot t3 = p) && (listequal(getgamma t1 , gamma)) && (listequal(getgamma t2 , gamma@[a])) && (listequal(getgamma t3 , gamma@[b]))) then (valid_ndprooftree t1) && (valid_ndprooftree t2) && (valid_ndprooftree t3) else false
                              | _ -> false
                            )
;;

(* ******************************************************************************************** *)
(*                                        Pad ND-Proof Tree                                     *)
(* ******************************************************************************************** *)
let rec pad tree g = match tree with
    LF(gamma,p) -> LF(union(gamma,g),p)
  | II(t,gamma,p) -> II((pad t g),union(gamma,g),p)
  | IE(t1,t2,gamma,p) -> IE((pad t1 g), (pad t2 g), union(gamma,g), p)
  | NI(t,gamma,p) -> NI((pad t g),union(gamma,g),p)
  | NC(t,gamma,p) -> NC((pad t g),union(gamma,g),p)
  | AI(t1,t2,gamma,p) -> AI((pad t1 g), (pad t2 g), union(gamma,g), p)
  | AEL(t,gamma,p) -> AEL((pad t g),union(gamma,g),p)
  | AER(t,gamma,p) -> AER((pad t g),union(gamma,g),p)
  | OIL(t,gamma,p) -> OIL((pad t g),union(gamma,g),p)
  | OIR(t,gamma,p) -> OIR((pad t g),union(gamma,g),p)
  | OE(t1,t2,t3,gamma,p) -> OE((pad t1 g), (pad t2 g), (pad t3 g), union(gamma,g), p)
;;


(* ******************************************************************************************** *)
(*                                        Prune ND-Proof Tree                                   *)
(* ******************************************************************************************** *)
let rec getdelta tree = match tree with
    LF(gamma,T) -> []
  | LF(gamma,p) -> [p]
  | II(t,gamma,p) -> getdelta t
  | IE(t1,t2,gamma,p) -> union(getdelta t1, getdelta t2)
  | NI(t,gamma,p) -> getdelta t
  | NC(t,gamma,p) -> getdelta t
  | AI(t1,t2,gamma,p) -> union(getdelta t1, getdelta t2)
  | AEL(t,gamma,p) -> getdelta t
  | AER(t,gamma,p) -> getdelta t
  | OIL(t,gamma,p) -> getdelta t
  | OIR(t,gamma,p) -> getdelta t
  | OE(t1,t2,t3,gamma,p) -> union(getdelta t1, union(getdelta t2, getdelta t3))
;;

let rec delete p l = match l with
    [] -> []
  | x::xs -> if x=p then (delete p xs) else (x::(delete p xs))
;;

(* Set Subtraction *)
let rec set_minus (s1,s2) = match s2 with
    [] -> s1
  | x::xs -> set_minus ((delete x s1), xs)
;;  


let rec prune_as_per_delta tree g delta = match tree with
      LF(gamma,p) -> LF(union(set_minus(gamma,g),delta) ,p)
    | II(t,gamma,p) -> II((prune_as_per_delta t g delta), union(set_minus(gamma,g),delta),p)
    | IE(t1,t2,gamma,p) -> IE((prune_as_per_delta t1 g delta), (prune_as_per_delta t2 g delta), union(set_minus(gamma,g),delta),p)
    | NI(t,gamma,p) -> NI((prune_as_per_delta t g delta), union(set_minus(gamma,g),delta),p)
    | NC(t,gamma,p) -> NC((prune_as_per_delta t g delta), union(set_minus(gamma,g),delta),p)
    | AI(t1,t2,gamma,p) -> AI((prune_as_per_delta t1 g delta), (prune_as_per_delta t2 g delta), union(set_minus(gamma,g),delta),p)
    | AEL(t,gamma,p) -> AEL((prune_as_per_delta t g delta), union(set_minus(gamma,g),delta),p)
    | AER(t,gamma,p) -> AER((prune_as_per_delta t g delta), union(set_minus(gamma,g),delta),p)
    | OIL(t,gamma,p) -> OIL((prune_as_per_delta t g delta), union(set_minus(gamma,g),delta),p)
    | OIR(t,gamma,p) -> OIR((prune_as_per_delta t g delta), union(set_minus(gamma,g),delta),p)
    | OE(t1,t2,t3,gamma,p) -> OE((prune_as_per_delta t1 g delta), (prune_as_per_delta t2 g delta), (prune_as_per_delta t3 g delta), union(set_minus(gamma,g),delta),p)
;;

(* Set Intersection *)
let rec intersection (s1,s2) = match s1 with
    [] -> []
  | x::xs -> if (List.mem x s2) then x::(intersection (xs,s2)) else (intersection (xs,s2))
;;

let prune tree = prune_as_per_delta tree (getgamma tree) (intersection(getgamma tree, getdelta tree))
;;


(* ******************************************************************************************** *)
(*                                        Graft ND-Proof Tree                                   *)
(* ******************************************************************************************** *)
let rec get_gammatree treelist p = match treelist with
    x::xs -> if (getroot x = p) then x else (get_gammatree xs p)
  | [] ->  raise EmptyList
;;

let rec graft_as_per_delta tree treelist gamma delta = match tree with
    LF(g,p) when (not(List.mem p delta)) -> LF(union(set_minus(g,delta),gamma),p)
  | LF(g,T) -> LF(union(set_minus(g,delta),gamma),T)
  | LF(g,p) -> if (List.mem p g) then (pad (get_gammatree treelist p) (set_minus (g, delta))) else (raise TreeNotValid)
  | II(t,g,p) -> II((graft_as_per_delta t treelist gamma delta),union(set_minus(g,delta),gamma),p)
  | IE(t1,t2,g,p) -> IE((graft_as_per_delta t1 treelist gamma delta), (graft_as_per_delta t2 treelist gamma delta), union(set_minus(g,delta),gamma), p)
  | NI(t,g,p) -> NI((graft_as_per_delta t treelist gamma delta),union(set_minus(g,delta),gamma),p)
  | NC(t,g,p) -> NC((graft_as_per_delta t treelist gamma delta),union(set_minus(g,delta),gamma),p)
  | AI(t1,t2,g,p) -> AI((graft_as_per_delta t1 treelist gamma delta), (graft_as_per_delta t2 treelist gamma delta), union(set_minus(g,delta),gamma), p)
  | AEL(t,g,p) -> AEL((graft_as_per_delta t treelist gamma delta),union(set_minus(g,delta),gamma),p)
  | AER(t,g,p) -> AER((graft_as_per_delta t treelist gamma delta),union(set_minus(g,delta),gamma),p)
  | OIL(t,g,p) -> OIL((graft_as_per_delta t treelist gamma delta),union(set_minus(g,delta),gamma),p)
  | OIR(t,g,p) -> OIR((graft_as_per_delta t treelist gamma delta),union(set_minus(g,delta),gamma),p)
  | OE(t1,t2,t3,g,p) -> OE((graft_as_per_delta t1 treelist gamma delta), (graft_as_per_delta t2 treelist gamma delta), (graft_as_per_delta t3 treelist gamma delta), union(set_minus(g,delta),gamma), p)
;;

let graft tree treelist = if (List.length treelist = 0) then (raise TreeDNE) else (graft_as_per_delta tree treelist (getgamma (List.hd treelist)) (getgamma tree))
;;

let rec find_rpair_wrapper tree = match tree with
    LF(gamma,p) -> []
  | II(t,gamma,p) -> find_rpair_wrapper t
  | IE(t1,t2,gamma,p) -> (
                            match t1 with
                              II(t3,g,Impl(p1,q1)) -> [tree]
                            | _ -> (
                                    let frt1 = (find_rpair_wrapper t1) in
                                    if(frt1 = []) then (find_rpair_wrapper t2) else (frt1)
                                   )
                         )
  | NI(t,gamma,p) -> find_rpair_wrapper t
  | NC(t,gamma,p) -> find_rpair_wrapper t
  | AI(t1,t2,gamma,p) -> (
                          let frt1 = (find_rpair_wrapper t1) in
                          if(frt1 = []) then (find_rpair_wrapper t2) else (frt1)
                         )
  | AEL(t,gamma,p) -> (
                        match t with
                          AI(t1,t2,g,And(p1,q1)) -> [tree]
                        | _ -> find_rpair_wrapper t
                      )
  | AER(t,gamma,p) -> (
                        match t with
                          AI(t1,t2,g,And(p1,q1)) -> [tree]
                        | _ -> find_rpair_wrapper t
                      )
  | OIL(t,gamma,p) -> find_rpair_wrapper t
  | OIR(t,gamma,p) -> find_rpair_wrapper t
  | OE(t1,t2,t3,gamma,p) -> (
                               match t1 with
                                 OIL(t,g,p1) ->[tree]
                               | OIR(t,g,p1) -> [tree]
                               | _ -> (
                                        let frt1 = (find_rpair_wrapper t1) and frt2 = (find_rpair_wrapper t2) in
                                        if(frt1 != []) then (frt1) else (if (frt2 != []) then (frt2) else (find_rpair_wrapper t3))
                                      )  
                            )
;;

let find_rpair tree = (
                        let frt = (find_rpair_wrapper tree) in
                        match frt with
                          [x] -> x
                        | _ -> raise AlreadyNormalised
                      )
;;


let simplify1 tree = match tree with
    AEL(t,gamma,p) -> (
                      match t with
                        AI(t1,t2,gamma,And(p1,q1)) -> t1
                      | _ -> raise RpairNotExist
                     )
  | AER(t,gamma,p) -> (
                        match t with
                          AI(t1,t2,gamma,And(p1,q1)) -> t2
                        | _ -> raise RpairNotExist
                      )
  | IE(t1,t2,gamma,p) -> graft t1 [t2]
  | OE(t1,t2,t3,gamma,p) -> (
                              match t1 with
                                OIL(t,g,And(a,b)) -> graft t2 [t]
                              | OIR(t,g,And(a,b)) -> graft t3 [t]
                              | _ -> raise RpairNotExist
                            )
  | _ -> raise RpairNotExist
;;

let rec normalise tree = match tree with
    AEL(t,gamma,p) -> (
                        match t with 
                          AI(t1,t2,g,p1) -> t1
                        | _ -> tree
                      )
  | AER(t,gamma,p) -> (
                        match t with
                        AI(t1,t2,g,p1) -> t2
                        | _ -> tree
                      )
  | IE(t1,t2,gamma,p) -> (
                            match t1 with
                              II(t,g,p1) -> graft t [t2]
                            | _ -> tree
                         )
  | OE(t1,t2,t3,gamma,p) -> (
                              match t1 with
                                OIL(t,g,p1) -> graft t2 [t]
                              | OIR(t,g,p1) -> graft t3 [t]
                              | _ -> tree
                            )
  | _ -> tree
;;


(* Test cases *)
(* Example *)
let p = L "p";;
let q = L "q";;

let gamma = [p; q];;
let anded = And(p, q);;

let e1 = AEL(AI(LF(gamma, p), LF(gamma, q), gamma, anded), gamma, p);;

find_rpair e1;;
simplify1 e1;;
normalise e1;;

(* Example 2 *)

let e2 = AER(AI(LF(gamma, p), LF(gamma, q), gamma, anded),gamma, q);;
find_rpair e2;;
simplify1 e2;;
normalise e2;;

