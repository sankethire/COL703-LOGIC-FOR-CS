(* ******************************************************************************************** *)
(*             ASSIGNMENT 0 : Syntax and Semantics of Propositional Logic                       *)
(* ******************************************************************************************** *)






(* ******************************************************************************************** *)
(*                                 Exceptions Defintion                                         *)
(* ******************************************************************************************** *)
exception DoNothing;;
exception NotSubProp;;
exception NotTF;;

(* ******************************************************************************************** *)
(*                                     Prop Definition                                          *)
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
(*                                 Max Implementation                                           *)
(* ******************************************************************************************** *)

let maximum a b = if (a > b) then a else b;;

(* ******************************************************************************************** *)
(*                                 RHO of (string -> prop)                                      *)
(* ******************************************************************************************** *)


let rho s = match s with
    "a" -> T
  | "b" -> T
  | "c" -> F
  | "d" -> T
  |_ -> raise DoNothing
;;

(* ******************************************************************************************** *)
(*                                 Height Implementation                                        *)
(* ******************************************************************************************** *)


let rec ht rho p = match p with
    T -> 0
  | F -> 0
  | L(s) -> ht rho (rho s) 
  | Not(q) -> 1 + (ht rho q)
  | And(q1,q2) -> 1 + (maximum (ht rho q1) (ht rho q2))
  | Or(q1,q2) -> 1 + (maximum (ht rho q1) (ht rho q2))
  | Impl(q1,q2) -> 1 + (maximum (ht rho q1) (ht rho q2))
  | Iff(q1,q2) -> 1 + (maximum (ht rho q1) (ht rho q2))
;;

(* ******************************************************************************************** *)
(*                                 Size Implementation                                          *)
(* ******************************************************************************************** *)


let rec size rho p = match p with
    T -> 1
  | F -> 1
  | L(s) -> size  rho (rho s)
  | Not(q) -> 1 + (size rho q)
  | And(q1,q2) -> 1 + (size rho q1) + (size rho q2)
  | Or(q1,q2) -> 1 + (size rho q1) + (size rho q2)
  | Impl(q1,q2) -> 1 + (size rho q1) + (size rho q2)
  | Iff(q1,q2) -> 1 + (size rho q1) + (size rho q2)
;;  

(* ******************************************************************************************** *)
(*                                 Remove List Duplicates Implementation                        *)
(* ******************************************************************************************** *)


  let make_unique xs x = if List.mem x xs then xs else x :: xs
  ;;
  
  let remove_duplicates xs = List.rev (List.fold_left make_unique [] xs)
  ;;
  

(* ******************************************************************************************** *)
(*                                 Letters Implementation                                       *)
(* ******************************************************************************************** *)


let rec letter rho l p = match p with
		  T -> l
		| F -> l
		| L(s) -> l@[s]
		| Not(q) -> letter rho l q
		| And(q1, q2) -> l@((letter rho [] q1)@(letter rho [] q2))
		| Or(q1, q2) -> l@((letter rho [] q1)@(letter rho [] q2))
		| Impl(q1, q2) -> l@((letter rho [] q1)@(letter rho [] q2))
		| Iff(q1, q2) -> l@((letter rho [] q1)@(letter rho [] q2))
;;

let letters p = remove_duplicates(letter rho [] p)


(* ******************************************************************************************** *)
(*                                 Subprop Implementation                                       *)
(* ******************************************************************************************** *)


let rec subprop1 p1 p2 l s = match (p1,p2) with
		(a,b) when (a=b) -> l@[s^"="]
		|(a,Not(b)) -> if(a=b) then l@[s^"3="] else (subprop1 a b l (s^"3"))
		|(a,And(b,c)) -> l@(subprop1 a b [] (s^"0"))@(subprop1 a c [] (s^"1"))
		|(a,Or(b,c)) -> l@(subprop1 a b [] (s^"0"))@(subprop1 a c [] (s^"1"))
		|(a,Impl(b,c)) -> l@(subprop1 a b [] (s^"0"))@(subprop1 a c [] (s^"1"))
		|(a,Iff(b,c)) -> l@(subprop1 a b [] (s^"0"))@(subprop1 a c [] (s^"1"))
		|_ -> []
;;

let subprop_at p1 p2 = 
	let a = subprop1 p1 p2 [] "" in 
    let b = List.length a in 
      if(b <> 0 || p1=p2) then (remove_duplicates(a)) else (raise NotSubProp)
;;


(* ******************************************************************************************** *)
(*                                 ARHO (string -> bool)                                        *)
(* ******************************************************************************************** *)


let arho s = match s with
"a" -> true
| "b" -> true
| "c" -> false 
| "d" -> true
| _ -> raise DoNothing
;;

let brho s = match s with
"a" -> true
| "b" -> false
| "c" -> false 
| "d" -> false
| _ -> raise DoNothing
;;

let crho s = match s with
"a" -> false
| "b" -> false
| "c" -> false 
| "d" -> false
| _ -> raise DoNothing
;;

let boolToProp b = match b with 
  true -> T
  |false -> F
;;
(* ******************************************************************************************** *)
(*                                 TRUTH Implementation                                         *)
(* ******************************************************************************************** *)

let rec truth p arho1 = match p with
    T -> true
  | F -> false
  | L(s) -> truth (boolToProp (arho1 s)) arho1
  | Not(q) -> not(truth q arho1)
  | And(q1,q2) -> (truth q1 arho1) && (truth q2 arho1)
  | Or(q1,q2) -> (truth q1 arho1) || (truth q2 arho1)
  | Impl(q1,q2) -> (not(truth q1 arho1)) || (truth q2 arho1) 
  | Iff(q1,q2) -> ((not(truth q1 arho1)) || (truth q2 arho1)) && ((not(truth q2 arho1)) || (truth q1 arho1))

(* ******************************************************************************************** *)
(*                                 NNF Implementation                                           *)
(* ******************************************************************************************** *)


let rec nnf p = match p with
    And(a,b) -> And(nnf a,nnf b)
  | Or(a,b) -> Or(nnf a,nnf b)
  | Impl(a,b) -> Or(nnf(Not a),nnf b)
  | Iff(a,b) -> Or(And(nnf a,nnf b),And(nnf(Not a),nnf(Not b)))
  | Not(T) -> F
  | Not(F) -> T
  | Not(Not a) -> nnf a
  | Not(And(a,b)) -> Or(nnf(Not a),nnf(Not b))
  | Not(Or(a,b)) -> And(nnf(Not a),nnf(Not b))
  | Not(Impl(a,b)) -> And(nnf a,nnf(Not b))
  | Not(Iff(a,b)) -> Or(And(nnf a,nnf(Not b)),And(nnf(Not a),nnf b))
  | _ -> p
;;

(* ******************************************************************************************** *)
(*                                 DNF Implementation                                           *)
(* ******************************************************************************************** *)
let rec distribution p = match p with
    And(a,(Or(b,c))) -> Or(distribution(And(a,b)),distribution(And(a,c)))
  | And(Or(a,b),c) -> Or(distribution(And(a,c)),distribution(And(b,c)))
  | _ -> p;;

let rec idnf p = match p with
    And(a,b) -> distribution(And(idnf a,idnf b))
  | Or(a,b) -> Or(idnf a,idnf b)
  | _ -> p;;

(* let dnf p = idnf (nnf p)
;; *)

(* let get_root p = match p with
   T -> "T"
  |F -> "F"
  |L(s) -> "L" 
  |Not(q) -> "Not"
  |And(q1,q2) -> "And"
  |Or(q1,q2) -> "Or"
  |Impl(q1,q2) -> "Impl"
  |Iff(q1,q2) -> "Iff"
;; *)

(* let dnf p = 
            (
              let p1 = (idnf (nnf p)) in
                if((get_root p1) = "Or") then p1 else (raise InConvertible)
            ) 
;;              *)

let dnf p = idnf (nnf p)
;;

(* ******************************************************************************************** *)

(* ******************************************************************************************** *)
(*                                     CNF Implementaion                                        *)
(* ******************************************************************************************** *)

let rec c_distribution p = match p with
    Or(a,(And(b,c))) -> And(c_distribution(Or(a,b)),c_distribution(Or(a,c)))
  | Or(And(a,b),c) -> And(c_distribution(Or(a,c)),c_distribution(Or(b,c)))
  | _ -> p;;

let rec icnf p = match p with
    Or(a,b) -> c_distribution(Or(icnf a,icnf b))
  | And(a,b) -> And(icnf a,icnf b)
  | _ -> p;;

let cnf p = icnf (nnf p)
;;

(* let cnf p = 
  (
    let p1 = (icnf (nnf p)) in
      if((get_root p1) = "And") then p1 else (raise InConvertible)
  ) 
;; *)


(* ******************************************************************************************** *)
(*                                           Examples                                           *)
(* ******************************************************************************************** *)


let t1 = And(L "a", L "b");;
let t2 = Or(L "d", L "a");;
let t3 = Impl(t1, t2);;


let a = And(T,F);;
let b = Or(F,T);;
let c = Impl(a,b);;
let d = Not(c);;

let aa = T;;
(* val aa : prop = T *)
let bb = F;;
(* val bb : prop = F *)
let cc = T;;
(* val cc : prop = T *)
let q = Or(aa,Or(bb,cc));;
(* val q : prop = Or (T, Or (F, T)) *)
nnf q;;
(* - : prop = Or (T, Or (F, T)) *)


(* ********************************************************* *)
(*                      ht examples                          *)
(* ********************************************************* *)
(* 
# ht;;
- : (string -> prop) -> prop -> int = <fun>
# ht rho a;;
- : int = 1
# ht rho b;;
- : int = 1
# ht rho c;;
- : int = 2
# ht rho d;;
- : int = 3
# ht rho t1;;
- : int = 1
# ht rho t2;;
- : int = 1
# ht rho t3;;
- : int = 2
# let m = Impl(t1,t3);;
val m : prop =
  Impl (And (L "a", L "b"), Impl (And (L "a", L "b"), Or (L "d", L "a")))
# ht rho m;;
- : int = 3
# let n = Not m;;
val n : prop =
  Not
   (Impl (And (L "a", L "b"), Impl (And (L "a", L "b"), Or (L "d", L "a"))))
# ht rho n;;
- : int = 4
*)
(* ********************************************************* *)
(*                     size Examples                         *)
(* ********************************************************* *)
(* 
# size rho a;;
- : int = 3
# size rho b;;
- : int = 3
# size rho c;;
- : int = 7
# size rho d;;
- : int = 8
# size rho t1;;
- : int = 3
# size rho t2;;
- : int = 3
# size rho t3;;
- : int = 7
# size rho (Impl(t1,t3));;
- : int = 11
# size rho (Not(Imple(t2,t3)));;
# size rho (Not(Impl(t1,t3)));; 
- : int = 12
*)
(* ********************************************************* *)
(*                  letters Examples                         *)
(* ********************************************************* *)
(* 
# letters;;
- : prop -> string list = <fun>
# letters t1;;
- : string list = ["a"; "b"]
# letters t2;;
- : string list = ["d"; "a"]
# letters t3;;
- : string list = ["a"; "b"; "d"]
# letters a;;
- : string list = []
# letters b;;
- : string list = []
# letters c;;
- : string list = []
# letters d;;
- : string list = []

*)

(* ********************************************************* *)
(*                   subprop_at Examples                        *)
(* ********************************************************* *)
(*
# subprop_at;;
- : prop -> prop -> string list = <fun> 
# subprop_at t1 t3;;
- : string list = ["0="]
# subprop_at T t3;;
Exception: NotSubProp.
# subprop_at t2 t3;;
- : string list = ["1="]
# subprop_at (L "a") t3;;
- : string list = ["00="; "11="]

*)

(* ********************************************************* *)
(*                   truth Examples                          *)
(* ********************************************************* *)
(* 
# truth;;
- : prop -> (string -> bool) -> bool = <fun>
# truth a arho;;
- : bool = false
# a;;
- : prop = And (T, F)
# truth b arho;;
- : bool = true
# truth c arho;;
- : bool = true
# c;;   
- : prop = Impl (And (T, F), Or (F, T))
# b;;
- : prop = Or (F, T)
# truth d arho;;
- : bool = false

-----------------------------------------------------------------
CONTINGENCY
-----------------------------------------------------------------

# truth t1 arho;;
- : bool = true
# truth t1 brho;;
- : bool = false
# truth t2 crho;;
- : bool = false
# truth t2 arho;;
- : bool = true


-----------------------------------------------------------------
CONTRADICTION
-----------------------------------------------------------------
# truth (And(a,Not a)) arho;;
- : bool = false
# truth (And(a,Not a)) brho;;
- : bool = false
# truth (Not((Iff(Impl(a,b), Impl(Not b, Not a))))) arho;;
- : bool = false
# truth (Not((Iff(Impl(a,b), Impl(Not b, Not a))))) brho;;
- : bool = false



-----------------------------------------------------------------
TAUTOLOGY
-----------------------------------------------------------------
# truth (Or(a,Not a)) arho;;
- : bool = true
# truth (Or(a,Not a)) brho;;
- : bool = true
# truth (Iff(Impl(a,b), Impl(Not b, Not a))) arho;;
- : bool = true
# truth (Iff(Impl(a,b), Impl(Not b, Not a))) brho;;
- : bool = true
# truth (Impl(And(Impl(Not a,b),Impl(Not a, Not b)),a)) arho;;
- : bool = true
# truth (Impl(And(Impl(Not a,b),Impl(Not a, Not b)),a)) brho;;
- : bool = true


*)

(* ********************************************************* *)
(*                    cnf, dnf and nnf                       *)
(* ********************************************************* *)
(* 
# let pp = Or(a,Or(b,c));;
val pp : prop = Or (And (T, F), Or (Or (F, T), Impl (And (T, F), Or (F, T))))
# cnf pp;;
- : prop =
And (Or (T, Or (Or (F, T), Or (Or (F, T), Or (F, T)))),
 Or (F, Or (Or (F, T), Or (Or (F, T), Or (F, T)))))
# aa;;
- : prop = T
# q;;
- : prop = Or (T, Or (F, T))
# cnf q;;
- : prop = Or (T, Or (F, T))
# a;;
- : prop = And (T, F)
# b;;
- : prop = Or (F, T)
# c;;
- : prop = Impl (And (T, F), Or (F, T))
# dnf q;;
- : prop = Or (T, Or (F, T))
# dnf pp;;
- : prop = Or (And (T, F), Or (Or (F, T), Or (Or (F, T), Or (F, T))))
# let qq = And(a,And(b,c));;
val qq : prop =
  And (And (T, F), And (Or (F, T), Impl (And (T, F), Or (F, T))))
# dnf qq;;
- : prop =
Or
 (Or (Or (And (And (T, F), And (F, F)), And (And (T, F), And (T, F))),
   Or (And (And (T, F), And (F, T)), And (And (T, F), And (T, T)))),
 Or (Or (And (And (T, F), And (F, F)), And (And (T, F), And (T, F))),
  Or (And (And (T, F), And (F, T)), And (And (T, F), And (T, T)))))
# let ww = And(aa,And(bb,cc));;
val ww : prop = And (T, And (F, T))
# dnf ww;;
- : prop = And (T, And (F, T))
# nnf a;;
- : prop = And (T, F)
# nnf d;;
- : prop = And (And (T, F), And (T, F))
# nnf ww;;
- : prop = And (T, And (F, T))
# nnf qq;;
- : prop = And (And (T, F), And (Or (F, T), Or (Or (F, T), Or (F, T))))

*)

(* *************************************************************************** *)

