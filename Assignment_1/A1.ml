(* ******************************************************************************************** *)
(*                                ASSIGNMENT 1 : Analytic Tableaux                              *)
(* ******************************************************************************************** *)



(* ******************************************************************************************** *)
(*                                 Exceptions Defintion                                         *)
(* ******************************************************************************************** *)
exception DoNothing;;
exception DoesNotExist;;
exception InvalidNode;;
exception InvalidTableaux;;

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
(*                                     Datatypes Declared                                       *)
(* ******************************************************************************************** *)
type proptruth = Proptruth of string * bool;;
(*    prop * truth * isexamined * isclosed    *)
type node = Node of prop * bool * bool * bool;;

type analyticTableaux =   Lf of node * (proptruth list) * (node list)
          | A of node * (proptruth list) * analyticTableaux * (node list)
          | B of node * (proptruth list) * analyticTableaux * analyticTableaux * (node list)
;;

(* ******************************************************************************************** *)
(*                                     Helper Functions                                         *)
(* ******************************************************************************************** *)
let get_first (x,y) = x;;
let get_second (x,y) = y;;
let get_tuple p = match p with Proptruth(a,b) -> (a,b);;
let rec ispresent proptruthlist p = if(List.length proptruthlist = 0) then false else (if(get_first(get_tuple(List.hd proptruthlist)) = p) then true else (ispresent (List.tl proptruthlist) p));;
let rec get_truth proptruthlist p = if(List.length proptruthlist = 0) then (raise DoesNotExist) else (if(get_first(get_tuple(List.hd proptruthlist)) = p) then (get_second(get_tuple(List.hd proptruthlist))) else (get_truth (List.tl proptruthlist) p));;


(* ******************************************************************************************** *)
(*                                        Step Develop                                          *)
(* ******************************************************************************************** *)
let rec step_develop tableaux = match tableaux with
      Lf(Node(a,b,c,true),pl,unexamined) -> tableaux
      (* if prop is T or F *)
    | Lf(Node(F,true,false,false),pl,unexamined) -> Lf(Node(F,true,true,true),pl,unexamined)
    | Lf(Node(T,false,false,false),pl,unexamined) -> Lf(Node(T,false,true,true),pl,unexamined)
    | Lf(Node(F,false,false,false),pl,[]) -> Lf(Node(F,false,true,false),pl,[])
    | Lf(Node(T,true,false,false),pl,[]) -> Lf(Node(T,true,true,false),pl,[])
    | Lf(Node(F,false,false,false),pl,n::nl) -> A(Node(F,false,true,false),pl,(step_develop(Lf(n,pl,nl))),n::nl)
    | Lf(Node(T,true,false,false),pl,n::nl) -> A(Node(T,true,true,false),pl,(step_develop(Lf(n,pl,nl))),n::nl)  
      (* if prop is a letter *)
    | Lf(Node(L(s),b,false,false),pl,[]) -> if(ispresent pl s) then (
                                                                      if((get_truth pl s) = b) then Lf(Node(L(s),b,true,false),pl,[])
                                                                                                else Lf(Node(L(s),b,true,true),pl,[])
                                                                    )
                                                               else Lf(Node(L(s),b,true,false),pl @ [Proptruth(s,b)],[])
    | Lf(Node(L(s),b,false,false),pl,n::nl) -> if(ispresent pl s) then (
                                                                          if((get_truth pl s) = b) then A(Node(L(s),b,true,false),pl,step_develop(Lf(n,pl,nl)),n::nl)
                                                                                                else Lf(Node(L(s),b,true,true),pl,n::nl)
                                                                       )
                                                                  else A(Node(L(s),b,true,false),pl,step_develop(Lf(n,pl @ [Proptruth(s,b)],nl)),n::nl)                                                                   
       (* Alpha nodes for Not, And, Or, Impl *)
    | Lf(Node(And(q1,q2),true,false,false),pl,unexamined) -> A(Node(And(q1,q2),true,true,false),pl,step_develop (Lf(Node(q1,true,false,false),pl,unexamined @ [Node(q2,true,false,false)])),unexamined)
    | Lf(Node(Or(q1,q2),false,false,false),pl,unexamined) -> A(Node(Or(q1,q2),false,true,false),pl,step_develop (Lf(Node(q1,false,false,false),pl,unexamined @ [Node(q2,false,false,false)])),unexamined)
    | Lf(Node(Impl(q1,q2),false,false,false),pl,unexamined) -> A(Node(Impl(q1,q2),false,true,false),pl,step_develop (Lf(Node(q1,true,false,false),pl,unexamined @ [Node(q2,false,false,false)])),unexamined)
    | Lf(Node(Not(q),b,false,false),pl,unexamined) -> A(Node(q,b,true,false),pl,step_develop (Lf(Node(q,not(b),false,false),pl,unexamined)),unexamined) 
      (* Beta nodes for And, Or, Impl *)
    | Lf(Node(And(q1,q2),false,false,false),pl,unexamined) -> B(Node(And(q1,q2),false,true,false),pl,step_develop (Lf(Node(q1,false,false,false),pl,unexamined)),step_develop (Lf(Node(q2,false,false,false),pl,unexamined)),unexamined)
    | Lf(Node(Or(q1,q2),true,false,false),pl,unexamined) -> B(Node(Or(q1,q2),true,true,false),pl,step_develop (Lf(Node(q1,true,false,false),pl,unexamined)),step_develop (Lf(Node(q2,true,false,false),pl,unexamined)),unexamined)
    | Lf(Node(Impl(q1,q2),true,false,false),pl,unexamined) -> B(Node(Impl(q1,q2),true,true,false),pl,step_develop (Lf(Node(q1,false,false,false),pl,unexamined)),step_develop (Lf(Node(q2,true,false,false),pl,unexamined)),unexamined)
    | Lf(Node(Iff(q1,q2),true,false,false),pl,unexamined) -> B(Node(Iff(q1,q2),true,true,false),pl,step_develop (Lf(Node(q1,true,false,false),pl,unexamined @ [Node(q2,true,false,false)])),step_develop (Lf(Node(q2,false,false,false),pl,unexamined @ [Node(q2,false,false,false)])),unexamined)
    | Lf(Node(Iff(q1,q2),false,false,false),pl,unexamined) -> B(Node(Iff(q1,q2),false,true,false),pl,step_develop (Lf(Node(q1,true,false,false),pl,unexamined @ [Node(q2,false,false,false)])),step_develop (Lf(Node(q2,false,false,false),pl,unexamined @ [Node(q2,true,false,false)])),unexamined)
    | _ -> raise InvalidNode    
;;

(* ******************************************************************************************** *)
(*                                        Contrad Path                                          *)
(* ******************************************************************************************** *)
let rec contrad_path tableaux = match tableaux with
    Lf(Node(T,false,a,b),pl,unexamined) -> Lf(Node(T,false,a,true),pl,unexamined)
  | Lf(Node(F,true,a,b),pl,unexamined) -> Lf(Node(F,true,a,true),pl,unexamined)
  | Lf(Node(L(s),a,b,c),pl,unexamined) -> if(ispresent pl s) then (
                                                                      if((get_truth pl s) = a) then tableaux else Lf(Node(L(s),a,b,true),pl,unexamined)
                                                                  )
                                                             else tableaux
  | A(nd,pl,at,unexamined) -> A(nd,pl,contrad_path at, unexamined)
  | B(nd,pl,atl,atr,unexamined) -> B(nd,pl,contrad_path atl, contrad_path atr, unexamined)
  | _ -> tableaux
;;

let rec generate_tableaux tableaux = match tableaux with
    Lf(nd,pl,unexamined) -> step_develop tableaux
  | A(nd,pl,at,unexamined) -> A(nd,pl,generate_tableaux at, unexamined)
  | B(nd,pl,atl,atr,unexamined) -> B(nd,pl, generate_tableaux atl, generate_tableaux atr, unexamined)
;;

(* ******************************************************************************************** *)
(*                                       Valid Tableau                                          *)
(* ******************************************************************************************** *)
let valid_tableau tableaux prop truth = if (generate_tableaux tableaux) = (step_develop (Lf(Node(prop,truth,false,false),[],[]))) then true else (raise InvalidTableaux)   
;;

(* ******************************************************************************************** *)
(*                                         Select Node                                          *)
(* ******************************************************************************************** *)
let rec select_node tableaux = match tableaux with
    Lf(Node(q,b,false,false),_,_) -> Node(q,b,false,false)
  | Lf(Node(_,_,_,true),_,_) -> raise InvalidNode
  | A(nd,pl,at,unexamined) -> select_node at
  | B(nd,pl,atl,atr,unexamined) -> (match atl with
                                   
                                      Lf(Node(_,_,_,true),_,_) -> select_node atr
                                     | _ -> select_node atl
                                   )
  | _ -> raise InvalidNode
;;

let rec noContradList tableaux = match tableaux with
    Lf(Node(_,_,_,true),pl,_) -> []
  | Lf(Node(_,_,_,false),pl,_) -> pl
  | A(nd,pl,at,unexamined) -> noContradList at
  | B(nd,pl,atl,atr,unexamined) -> (
                                      match (noContradList atl) with
                                          [] -> noContradList atr
                                        | _ -> noContradList atl
                                   )
(* ******************************************************************************************** *)
(*                            Check Tautology And Contradiction                                 *)
(* ******************************************************************************************** *)                        
let rec check_tautology prop = noContradList (step_develop (Lf(Node(prop,false,false,false),[],[])));;
let rec check_contradiction prop = noContradList (step_develop (Lf(Node(prop,true,false,false),[],[])));;

let rec tableau_assignments_list tableaux = match tableaux with 
    Lf(Node(_,_,_,true),_,_) -> [[]]
  | Lf(Node(_,_,_,false),pl,_) -> [pl]
  | A(_,_,at,_) -> tableau_assignments_list at
  | B(_,_,atl,atr,_) -> (tableau_assignments_list atl) @ (tableau_assignments_list atr)

(* ******************************************************************************************** *)
(*                                     Find Assignments                                         *)
(* ******************************************************************************************** *)
let find_assignments prop truth = tableau_assignments_list (step_develop (Lf(Node(prop,truth,false,false),[],[])));;

let a = [Proptruth("a",true); Proptruth("b",false); Proptruth("c",true)];;


(* ******************************************************************************************** *)
(*                                         Examples                                             *)
(* ******************************************************************************************** *)
(* Tautology And Contradiction Checking *)
let b = Impl(And(Impl(L "a", L "b"),Impl(L "b", L "c")),Impl(L "a",L "c"));;

check_tautology b;;
check_tautology (Not(b));;
check_contradiction b;;
check_contradiction (Not(b));;

(* 
# check_tautology b;;
- : proptruth list = []
# check_tautology (Not(b));;
- : proptruth list = [Proptruth ("a", true); Proptruth ("b", false)]
# check_contradiction b;;
- : proptruth list = [Proptruth ("a", true); Proptruth ("b", false)]
# check_contradiction (Not(b));;
- : proptruth list = []
*)

(* ===================================================================================================== *)