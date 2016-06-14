(* Hansei as a logic programming language
   Emulating logic variables: the append _relation_ 
*)

(* When working at the top-level, do:
#load "delimcc.cma";;
#load "prob.cma";;
*)
open ProbM;;

(* We define boolean lists with a non-deterministic spine *)
(* The elements could be non-deterministic too. 
   We have used such lists already in Hansei: see slazy.ml
   and music1.ml.
   See our ICFP09 paper for discussion of such non-deterministic
   data structures.
*)

let letlazy = ProbM.letlazy_nesting;;	(* for the sake of committed choice *)


type bl = Nil | Cons of bool * blist
and blist = unit -> bl;;

(* Easy-to-use constructors of the lists *)
let nil  : blist = fun () -> Nil;;
let cons : bool -> blist -> blist = fun h t () -> Cons (h,t);;


(* Conversion to fully deterministic lists, so that we can display
   the result.
*)
let rec list_of_blist bl =
  match bl () with
  | Nil        -> []
  | Cons (h,t) -> h:: list_of_blist t
;;

(* We now define append, seemingly as a function. *)
let rec append l1 l2 =
  match l1 () with
  | Nil        -> l2
  | Cons (h,t) -> cons h (fun () -> append t l2 ())
;;

(* Sample boolean lists, to be used in the examples *)
let t3 = cons true (cons true (cons true nil));;
let f2 = cons false (cons false nil);;

let [true; true; true] = list_of_blist t3;;

let [false; false] = list_of_blist f2;;

(* ?- append([t,t,t],[f,f],X). *)

(* Executing the append by itself *)
append t3 f2;;
(*
- : blist = <fun>
*)
(* does not give an informative answer. We have to run the model, 
   obtaining the set of answers, along with their weights (probabilities).
   We define the function for iterative deepening (a variation
   of the standard Hansei inference function discarding the continuation.)
   The first argument is the depth search bound (infinite, if None).
*)

let reify_part bound model =
  let f = fun acc -> function (p,Ptypes.V x) -> (p,x)::acc | _ -> acc in
  List.fold_left f [] (Inference.explore bound (reify0 model));;

let [(1., [true; true; true; false; false])] =
  reify_part None (fun () ->
    list_of_blist (append t3 f2));;

(* That was not surprising. We now model passing of logic variables
   as arguments of append.
*)

(* In Prolog, we can do
?- bool(X), append([X],[f,f],R).
X = t,
R = [t, f, f] ;
X = f,
R = [f, f, f].
*)

(* We try the same in Hansei *)
let 
[(0.25, ([false], [false; false; false]));
 (0.25, ([false], [true; false; false]));
 (0.25, ([true], [false; false; false]));
 (0.25, ([true], [true; false; false]))]
=
reify_part None (fun () ->
  let l = fun () -> Cons (flip 0.5, nil) in
  list_of_blist l, list_of_blist (append l f2)
);;

(* The result is wrong! What happened? We need memoization *)


(* We introduce the generators for the domains of bool and bool lists *)
(* We must use letlazy: a `logic variable', once determined, stays the same. *)

let a_boolean () = letlazy (fun () -> flip 0.5);;

let rec a_blist () =
  letlazy (fun () ->
    dist [(0.5, Nil);
	  (0.5, Cons(flip 0.5, a_blist ()))]);;
  
(* We check the generator *)
let [(0.5, []); (0.125, [false]); (0.03125, [false; false]);
     (0.03125, [false; true]); (0.125, [true]); (0.03125, [true; false]);
     (0.03125, [true; true])] =
reify_part (Some 5) (fun() -> list_of_blist (a_blist ()));;

(* We re-do the Prolog example
?- bool(X), append([X],[f,f],R).
X = t,
R = [t, f, f] ;
X = f,
R = [f, f, f].
*)

(* We try the same in Hansei *)
let [(0.5, ([false], [false; false; false]));
     (0.5, ([true], [true; false; false]))]
=
reify_part None (fun () ->
  let l = letlazy (fun () -> Cons (flip 0.5, nil)) in
  list_of_blist l, list_of_blist (append l f2)
);;


(* ?- append([t,t,t],X,R). *)
(* or, actually *)
(* ?- append([t,t,t],X,R), boollist(X), boollist(R). *)

let [(0.5, [true; true; true]); (0.125, [true; true; true; false]);
     (0.03125, [true; true; true; false; false]);  
     (0.03125, [true; true; true; false; true]);
     (0.125, [true; true; true; true]);
     (0.03125, [true; true; true; true; false]);
     (0.03125, [true; true; true; true; true])] =
reify_part (Some 5) (fun() ->
  let x = a_blist () in
  list_of_blist (append t3 x)
);;


(* ?- append(X,[f,f],R), boollist(X), boollist(R). *)

let [(0.5, [false; false]); (0.125, [false; false; false]);
     (0.03125, [false; false; false; false]);
     (0.03125, [false; true; false; false]); (0.125, [true; false; false]);
     (0.03125, [true; false; false; false]);
     (0.03125, [true; true; false; false])] =
reify_part (Some 5) (fun() ->
  let x = a_blist () in
  list_of_blist (append x f2)
);;

(* Running append `backwards' *)

(* We define a sample list to deconstruct *)
let t3f2 = append t3 f2;;

(* and the comparison function *)
let rec bl_compare l1 l2 =
  match (l1 (), l2 ()) with
  | (Nil,Nil) -> true
  | (Cons (h1,t1), Cons (h2,t2)) ->
      h1 = h2 && bl_compare t1 t2
  | _ -> false
;;


(* ?- append([t,t],X,[t,t,t,f,f]). *)

(* Exhaustive search *)
let [(0.0078125, [true; false; false])] =
reify_part None (fun() ->
  let x = a_blist () in
  let r = append (cons true (cons true nil)) x in
  if not (bl_compare r t3f2) then fail ();
  list_of_blist x
);;

(* ?- append(X,[f,f],[t,t,t,f,f]). *)

let [(0.0078125, [true; true; true])] =
reify_part None (fun() ->
  let x = a_blist () in
  let r = append x (cons false (cons false nil)) in
  if not (bl_compare r t3f2) then fail ();
  list_of_blist x
);;


(* Split the list into a prefix and a suffix *)
(* ?- append(X,Y,[t,t,t,f,f]). *)

let [(0.000244140625, ([], [true; true; true; false; false]));
     (0.000244140625, ([true], [true; true; false; false]));
     (0.000244140625, ([true; true], [true; false; false]));
     (0.000244140625, ([true; true; true], [false; false]));
     (0.000244140625, ([true; true; true; false], [false]));
     (0.000244140625, ([true; true; true; false; false], []))] =
reify_part None (fun() ->
  let x = a_blist () in
  let y = a_blist () in
  let r = append x y in
  if not (bl_compare r t3f2) then fail ();
  (list_of_blist x, list_of_blist y)
);;


(* last(E,L) :- append(_,[E],L). *)

let last bl = 
  let x = a_blist () in
  let e = a_boolean () in
  if not (bl_compare (append x (cons (e ()) nil)) bl) then fail ();
  e
;;

let [(0.0009765625, false)] =
reify_part None (fun() ->
  last t3f2 ()
);;


(* Some future work remains: *)

(* Although the following gives a finite failure: *)
let [(2.384185791015625e-07, [true; true; true; false; false])] =
reify_part None (fun () ->
  let x = a_blist () in
  let y = a_blist () in
  if not (bl_compare x t3f2) then fail ();
  if not (bl_compare x y) then fail ();
  list_of_blist y
);;

(* A slight modification leads to divergence.
   How could we make the rearrangement automatic?
   Update Hansei to distinguish letlazy computations with
   a special type? That would help solve the repeated sharing problem, too.
*)
let [(2.384185791015625e-07, [true; true; true; false; false])] =
reify_part (Some 30) (fun () ->
  let x = a_blist () in
  let y = a_blist () in
  if not (bl_compare x y) then fail ();
  if not (bl_compare x t3f2) then fail ();
  list_of_blist y
);;

(* Diverges *)
(* reify_part None (fun () -> *)
(*   let x = a_blist () in *)
(*   let y = a_blist () in *)
(*   if not (bl_compare x y) then fail (); *)
(*   if not (bl_compare x t3f2) then fail (); *)
(*   list_of_blist y *)
(* );; *)

(* The list deletion example and the committed choice *)

(* In Prolog

del([H|T],H,T).
del([H|T],D,[H|R]) :- del(T,D,R).
*)

let rec del : blist -> bool -> blist = fun l b ->
  match l () with
  | Cons (h,t) -> if h = b then t else cons h (del t b)
  | Nil -> fail ()
;;

(* The result of the deletion from a list shows only one choice, 
   reached with the Prob 1: the computation is fully deterministic.
*)
let [(1., [true; true; false; false])]
    =
  reify_part None @@ fun () -> 
    list_of_blist @@ del t3f2 true


let [(1., [true; true; true; false])]
    =
  reify_part None @@ fun () -> 
    list_of_blist @@ del t3f2 false


let ftf = cons false @@ cons true @@ cons false @@ nil

(* Attempting to run del backwards. We use explicit Cons to delay the
   flip until it is needed. 
*)
let [(0.25, ([false], [])); (0.25, ([true], []))]
    =
  reify_part None @@ fun () -> 
    let l = fun () -> Cons (flip 0.5, nil) in
    (list_of_blist l, list_of_blist @@ del l true)

(* the result is strange. We need laziness *)

let [(0.5, ([true], []))] =
  reify_part None @@ fun () -> 
    let l = letlazy @@ fun () -> Cons (flip 0.5, nil) in
    (list_of_blist l, list_of_blist @@ del l true)

let [(0.03125, ([false; true], [false])); (0.125, ([true], []));
     (0.03125, ([true; false], [false])); (0.03125, ([true; true], [true]))]
    =
  reify_part (Some 5) @@ fun () -> 
    let l = a_blist () in
    (list_of_blist l, list_of_blist @@ del l true)

let rec list_haslen : blist -> int -> unit = fun l n ->
  match (l (),n) with
  | (Nil,0)                    -> ()
  | (Cons (_,t),n) when n > 0 -> list_haslen t (n-1)
  | _                          -> fail ()



(* Running prog3 on all lists of length 3 *)
(* We run without the upper bound on the search, and it terminates! *)
(* We get all possible lists of three elements, with the exception
   of the list with all false, where del true fails.
   We can recover from the failure: see below for soft-cut
*)
let [(0.0078125, ([false; false; true], [false; false]));
     (0.0078125, ([false; true; false], [false; false]));
     (0.0078125, ([false; true; true], [false; true]));
     (0.0078125, ([true; false; false], [false; false]));
     (0.0078125, ([true; false; true], [false; true]));
     (0.0078125, ([true; true; false], [true; false]));
     (0.0078125, ([true; true; true], [true; true]))]
    =
  reify_part None @@ fun () -> 
    let l = a_blist () in
    list_haslen l 3;
    (list_of_blist l, list_of_blist @@ del l true)

(*
prog1(L,S) :- (del(L,true,LRem), S=deleted(LRem));
              S=failed.

%% ?- prog1([false,true,false],S).
%% S = deleted([false, false]) ;
%% S = failed.

%% ?- prog1(L,S).
%% L = [true|_G16],
%% S = deleted(_G16) ;
%% L = [_G15, true|_G19],
%% S = deleted([_G15|_G19]) ;
%% L = [_G15, _G21, true|_G25],
%% S = deleted([_G15, _G21|_G25]) ;
%% L = [_G15, _G21, _G27, true|_G31],
%% S = deleted([_G15, _G21, _G27|_G31]) 

% Committed choice
prog3(L,S) :- del(L,true,LRem) -> S=deleted(LRem); S=failed.

% When we run prog3 backwards, many choices are missing.
 
%% ?- prog3([true,false,true],S).
%% S = deleted([false, true]).

%% ?- prog3(L,S).
%% L = [true|_G16],
%% S = deleted(_G16).

%% ?- prog3([false,false,true,false],S).
%% S = deleted([false, false, false]).

*)

let soft_cut : (unit -> 'a) -> ('a -> 'w) -> (unit -> 'w) -> 'w =
  fun p q r ->
    match Inference.first_success (reify0 p) with
    | [] -> r ()
    | t  -> q (reflect t)
;;

let prog3 : blist -> blist option = fun l ->
  soft_cut (fun () -> del l true) (fun l -> Some l) (fun () -> None)


let [(1., Some [false; false])] =
  reify_part None @@ fun () -> 
    match prog3 (cons false @@ cons true @@ cons false @@ nil) with
    | None -> None
    | Some l -> Some (list_of_blist l)


let [(0.5, ([], None)); (0.125, ([false], None));
 (0.03125, ([false; false], None));
 (0.0078125, ([false; false; false], None));
 (0.001953125, ([false; false; false; false], None));
 (0.0078125, ([false; false; true], Some [false; false]));
 (0.03125, ([false; true], Some [false]));
 (0.0078125, ([false; true; false], Some [false; false]));
 (0.0078125, ([false; true; true], Some [false; true]));
 (0.125, ([true], Some [])); (0.03125, ([true; false], Some [false]));
 (0.0078125, ([true; false; false], Some [false; false]));
 (0.0078125, ([true; false; true], Some [false; true]));
 (0.03125, ([true; true], Some [true]));
 (0.0078125, ([true; true; false], Some [true; false]));
 (0.0078125, ([true; true; true], Some [true; true]))]
    =
  reify_part (Some 9) @@ fun () -> 
    let l = a_blist () in
    let r = match prog3 l with
    | None -> None
    | Some l -> Some (list_of_blist l)
    in (list_of_blist l, r)


(* Running prog3 on all lists of length 3 *)
(* We run without the upper bound on the search, and it terminates! *)
let [(0.0078125, ([false; false; false], None));
 (0.0078125, ([false; false; true], Some [false; false]));
 (0.0078125, ([false; true; false], Some [false; false]));
 (0.0078125, ([false; true; true], Some [false; true]));
 (0.0078125, ([true; false; false], Some [false; false]));
 (0.0078125, ([true; false; true], Some [false; true]));
 (0.0078125, ([true; true; false], Some [true; false]));
 (0.0078125, ([true; true; true], Some [true; true]))]
    =
  reify_part None @@ fun () -> 
    let l = a_blist () in
    list_haslen l 3;
    let r = match prog3 l with
    | None -> None
    | Some l -> Some (list_of_blist l)
    in (list_of_blist l, r)
;;

print_endline "\nAll done";;
