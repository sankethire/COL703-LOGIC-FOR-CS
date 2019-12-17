exception InConvertible;;
exception AnySatError;;
exception Indeterminate;;
exception NoTruthval;;

type prop =   T 
            | F 
            | L of int
            | Not of prop
            | And of prop * prop
            | Or of prop * prop
            | Impl of prop * prop
            | Iff of prop * prop
;;

type ilh = int * int * int;;

type t_table = (int, ilh) Hashtbl.t;;
type h_table = (ilh, int) Hashtbl.t;;

let get_t_table th_robdd = match th_robdd with
  (t,h) -> t
;;

let get_h_table th_robdd = match th_robdd with
  (t,h) -> h
;;

let insert_to_th th_robdd ilh1 = let i = Hashtbl.length (get_t_table th_robdd) in 
                                 let t_insert = Hashtbl.add (get_t_table th_robdd) i ilh1 and h_insert = Hashtbl.add (get_h_table th_robdd) ilh1 i in i
;;

let var table nd  = match (Hashtbl.find table nd) with (i,_,_) -> i;;
let low table nd  = match (Hashtbl.find table nd) with (_,l,_) -> l;;
let high table nd  = match (Hashtbl.find table nd) with (_,_,h) -> h;;

let lookup table ilh1 = Hashtbl.find table ilh1;;
let member table ilh1 = Hashtbl.mem table ilh1;;
let insert table ilh1 nd = Hashtbl.add table ilh1 nd;;

let mk th_robdd (i,l,h) = if (l=h) then l
                          else if (member (get_h_table th_robdd) (i,l,h)) then (lookup (get_h_table th_robdd) (i,l,h))
                          else insert_to_th th_robdd (i,l,h)
;;

let rec substitution p i j = match p with
    T -> T
  | F -> F
  | L(n) -> if(i=n) then j else p
  | Not(a) -> Not(substitution a i j)
  | And(a,b) -> And((substitution a i j),(substitution b i j))
  | Or(a,b) -> Or((substitution a i j),(substitution b i j))
  | Impl(a,b) -> Impl((substitution a i j),(substitution b i j))
  | Iff(a,b) -> Iff((substitution a i j),(substitution b i j))
;;

let rec truth p = match p with
    T -> true
  | F -> false
  | Not(q) -> not(truth q)
  | And(q1,q2) -> (truth q1) && (truth q2)
  | Or(q1,q2) -> (truth q1) || (truth q2)
  | Impl(q1,q2) -> (not(truth q1)) || (truth q2) 
  | Iff(q1,q2) -> ((not(truth q1)) || (truth q2)) && ((not(truth q2)) || (truth q1))
  | L(n) -> raise NoTruthval
;;

let rec build_dash th_robdd t i n = if(i>n) then if(not(truth t)) then 0 else 1
                                    else let v_0 = (build_dash th_robdd (substitution t i F) (i+1) n) and v_1 = (build_dash th_robdd (substitution t i T) (i+1) n)
                                    in (mk th_robdd (i,v_0,v_1))
;;

let build th_robdd t n = build_dash th_robdd t 1 n
;;

let is_zero_one nd = match nd with 
  | 0 -> true | 1 -> true
  | _ -> false
;;


let rec app t_tbl h_tbl op u1 u2 g = if(Hashtbl.mem g (u1,u2)) then Hashtbl.find g (u1,u2)
                                     else let u = 
                                        if((is_zero_one u1) && (is_zero_one u2)) then op u1 u2
                                        else if((var t_tbl u1)=(var t_tbl u2)) then (mk (t_tbl,h_tbl) ((var t_tbl u1), (app t_tbl h_tbl op (low t_tbl u1) (low t_tbl u2) g), (app t_tbl h_tbl op (high t_tbl u1) (high t_tbl u2) g)))
                                        else if((var t_tbl u1)<(var t_tbl u2)) then (mk (t_tbl,h_tbl) ((var t_tbl u1), (app t_tbl h_tbl op (low t_tbl u1) u2 g), (app t_tbl h_tbl op (high t_tbl u1) u2 g)))
                                        else (mk (t_tbl,h_tbl) ((var t_tbl u2), (app t_tbl h_tbl op u1 (low t_tbl u2) g), (app t_tbl h_tbl op u1 (high t_tbl u2) g)))
                                     in let add_to_g = Hashtbl.add g (u1,u2) u in u
;;

let apply th_robdd op u1 u2 = let g = Hashtbl.create 100 in (app (get_t_table th_robdd) (get_h_table th_robdd) op u1 u2 g)
;;

let rec restrict (t_tbl,h_tbl) (u,j,b) = if((var t_tbl u) > j) then u
                                     else if((var t_tbl u) < j) then (mk (t_tbl,h_tbl) ((var t_tbl u), (restrict (t_tbl,h_tbl) ((low t_tbl u),j,b)), (restrict (t_tbl,h_tbl) ((high t_tbl u),j,b)))) 
                                     else if(((var t_tbl u) = j) && (b=0)) then (restrict (t_tbl,h_tbl) ((low t_tbl u),j,b))  
                                     else (restrict (t_tbl,h_tbl) ((high t_tbl u),j,b))
;;

let rec power a b = match (a,b) with
    (0,0) -> raise Indeterminate
  | (c,0) -> 1
  | (c,d) -> a * (power a (b-1)) 
;;

let rec count t_tbl u = if(u=0) then 0
                        else if(u=1) then 1
                        else ((power 2 ((var t_tbl (low t_tbl u)) - (var t_tbl u) - 1)) * (count t_tbl (low t_tbl u))) + ((power 2 ((var t_tbl (high t_tbl u)) - (var t_tbl u) - 1)) * (count t_tbl (high t_tbl u)))
;;

let satcount t_tbl u = (power 2 ((var t_tbl u) - 1)) * (count t_tbl u)
;;

let rec anysat t_tbl u = if(u=0) then (raise AnySatError)
                         else if(u=1) then []
                         else if((low t_tbl u) = 0) then (var t_tbl u,1)::(anysat t_tbl (high t_tbl u))
                         else (var t_tbl u, 0)::(anysat t_tbl (low t_tbl u))
;;

let rec add_all (vrbl, boolval) lis = match lis with 
    [] -> []
  | x::xs -> ((vrbl,boolval)::x)::(add_all (vrbl,boolval) xs)
;;

let rec allsat t_tbl u = if(u=0) then []
                         else if(u=1) then [[]]
                         else (add_all ((var t_tbl u), 0) (allsat t_tbl (low t_tbl u))) @ (add_all ((var t_tbl u), 1) (allsat t_tbl (high t_tbl u))) 
;;

let rec sim t_tbl h_tbl d u = if(d=0) then 0
                              else if(u<=1) then u
                              else if(d=1) then (mk (t_tbl,h_tbl) ((var t_tbl u), (sim t_tbl h_tbl d (low t_tbl u)), (sim t_tbl h_tbl d (high t_tbl u)))) 
                              else if(var t_tbl d = var t_tbl u) then if(low t_tbl d = 0) then (sim t_tbl h_tbl (high t_tbl d) (high t_tbl u))
                                                                      else if(high t_tbl d = 0) then (sim t_tbl h_tbl (low t_tbl d) (low t_tbl u))
                                                                      else (mk (t_tbl,h_tbl) ((var t_tbl u), (sim t_tbl h_tbl (low t_tbl d) (low t_tbl u)), (sim t_tbl h_tbl (high t_tbl d) (high t_tbl u))))
                              else if(var t_tbl d < var t_tbl u) then (mk (t_tbl,h_tbl) ((var t_tbl u), (sim t_tbl h_tbl (low t_tbl d) u), (sim t_tbl h_tbl (high t_tbl d) u)))
                              else (mk (t_tbl,h_tbl) ((var t_tbl u), (sim t_tbl h_tbl d (low t_tbl u)), (sim t_tbl h_tbl d (high t_tbl u))))
;;

let simplify th_robdd d u = sim (get_t_table th_robdd) (get_h_table th_robdd) d u
;;


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

let get_root p = match p with
   T -> "T"
  |F -> "F"
  |L(s) -> "L" 
  |Not(q) -> "Not"
  |And(q1,q2) -> "And"
  |Or(q1,q2) -> "Or"
  |Impl(q1,q2) -> "Impl"
  |Iff(q1,q2) -> "Iff"
;;

let dnf p = 
            (
              let p1 = (idnf (nnf p)) in
                if((get_root p1) = "Or") then p1 else (raise InConvertible)
            ) 
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

(* let cnf p = icnf (nnf p)
;; *)

let cnf p = 
  (
    let p1 = (icnf (nnf p)) in
      if((get_root p1) = "And") then p1 else (raise InConvertible)
  ) 
;;



(* ***************************************************** *)
(*                   Test Cases                          *)
(* ***************************************************** *)

let n = 3;;
let thash = Hashtbl.create 10;;
Hashtbl.add thash 0 (n+1,-1,-1);;
Hashtbl.add thash 1 (n+1,-1,-1);;
let hhash = Hashtbl.create 10;;
let robdd1 = (thash,hhash)

(*
 Ordering: x1 < x2 < x3
 *)
 let vx1 = L(1);;
 let vx2 = L(2)
 let vx3 = L(3);;
 
 let p0 = Iff(vx1, vx2);;
 let p1 = Or(p0,vx3);;
 let p2 = Or(vx2,vx3);;
 let np1 = Not(p1);;
 
 (* compute NNF, CNF of p1 and Not(p1) *)
 let p1' = nnf(p1);;
 let p1'' = cnf(p1);;
 let np1' = nnf(np1);;
 let np1'' = cnf(np1);;
 
 (* build ROBDDs *)
 let tt = build robdd1 T 0;;
 let tf = build robdd1 F 0;;
 
 let tvx1 = build robdd1 vx1 1;;
 let tp2 = build robdd1 p2 3;;
 let tp0 = build robdd1 p0 3;;
 let tp1 = build robdd1 p1 3;;
 let tp1' = build robdd1 p1' 3;;
 let tp1'' = build robdd1 p1'' 3;;
 
 let tnp1 = build robdd1 np1 3;;
 let tnp1' = build robdd1 np1' 3;;
 let tnp1'' = build robdd1 np1'' 3;;
 
 (* Testcase #1 *)
 tp1 == tp1';;
 tp1 == tp1'';;
 tnp1 == tnp1';;
 tnp1 == tnp1'';;
 
 (* Testcase #2 *)

let op_and a b = if(a=1 && b=1) then 1 else 0;;
let op_or a b = if(a=1 || b=1) then 1 else 0;; 

 let tp1anp1 = apply robdd1 op_and tp1 tnp1;;
 tp1anp1 == tf;;
 let tp1onp1 = apply robdd1 op_or tp1 tnp1;;
 tp1onp1 == tt;;
 
 (* Testcase #3 *)
 let tp1rv30 = restrict robdd1 (tp1, 3, 0);;
 tp1rv30 == tp0;;
 let tp1rv31 = restrict robdd1 (tp1, 3, 1);;
 tp1rv31 =  tt;;
 
 (* Testcase #4 *)
 allsat (get_t_table robdd1) tp1;; (* 4 solutions: { {x1 = 0, x2 = 0}, {x1 = 1, x2 = 1}, {x1 = 1, x2 = 0, x3 = 1}, {x1 = 0, x2 = 1, x3 = 1}} *)
 anysat (get_t_table robdd1) tp1;; (* any of the above *)
 
 (* Testcase #5 *)
 let tstp2tp1 = simplify robdd1 tp2 tp1;;
 tstp2tp1 == tt;;
 let tstvx1tp1 = simplify robdd1 tvx1 tp1;;
 tstvx1tp1 == tp2;;    
