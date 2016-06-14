(* Type inference for the simply-typed lambda-calculus
              Forwards and Backwards
*)

open ProbM;;
(*
#load "prob.cma";;
*)

(* Preliminaries (declarations and printers) *)
(* There are OCaml `macros' to derive the printers automatically. *)

(* The data type of terms *)
(* Terms can be `read on-demand' (compare to stream) *)
type varname = string
type term_v = 
  | I of int 
  | V of varname 
  | L of varname * term 		(* abstractions *)
  | A of term * term			(* applications *)
and term  = unit -> term_v
;;

(* Nicer term constructors *)
let [vf;vx;vz;vu] = List.map (fun x -> fun () -> V x) ["f";"x";"z";"u"];;
let (%) e1 e2 = fun () -> A (e1,e2);;  (* Application: left-associative *)
let lam v t = fun () -> L (v,t);;
let num x = fun () -> I x;;		(* integer literal *)

(* Nice printing out of terms, with no extra parentheses *)

let paren test str = if test then "(" ^ str ^ ")" else str
;;

let string_of_term : term -> string =
  let rec loop prec = function
    | I n        -> string_of_int n
    | V name     -> name
    | L (v,body) -> paren (prec > 0) ("L" ^ v ^ ". " ^ loop 0 (body ()))
    | A (f,x)    -> paren (prec > 10) (loop 10 (f ()) ^ " " ^ loop 11 (x ()))
  in fun term -> loop 0 (term ())
;;

(* Generator of terms *)
(* The distribution of variables, geometric 0.1, is _infinite_ *)
let a_term () : term =
  let var () = "x" ^ string_of_int (geometric 0.1) in
  let rec loop () =
    dist [(0.1, fun () -> I 1);
	  (0.1, fun () -> V (var ()));
	  (0.4, fun () -> L (var (), letlazy loop));
	  (0.4, fun () -> A (letlazy loop, letlazy loop));] 
      ()
  in letlazy loop
;;

(* Run the computation up to a given depth and show only
   answers
*)
let run bound m =
  let f = fun acc -> function (p,Ptypes.V x) -> (p,x)::acc | _ -> acc in
  List.fold_left f [] (Inference.explore bound
		(reify0 m));;

(* It generates good terms and lots of nonsense *)
run (Some 5) (fun () -> string_of_term (a_term ()));;
(*
[(0.000160000000000000067, "(Lx0. 1) 1"); (0.1, "1");
 (0.000160000000000000067, "1 (1 1)");
 (0.000160000000000000067, "1 (Lx0. 1)"); (0.00400000000000000095, "1 1");
 (0.000160000000000000067, "1 1 1"); (0.000400000000000000128, "1 x0");
 (0.000360000000000000131, "1 x1"); (0.00400000000000000095, "Lx0. 1");
 (0.000160000000000000067, "Lx0. 1 1"); (0.000400000000000000128, "Lx0. x0");
 (0.00360000000000000077, "Lx1. 1"); (0.00324000000000000069, "Lx2. 1");
 (0.0100000000000000019, "x0"); (0.000400000000000000128, "x0 1");
 (0.00900000000000000105, "x1"); (0.000360000000000000077, "x1 1");
 (0.0081000000000000013, "x2"); (0.00729000000000000221, "x3")]
*)
  
  
(* The language of types: base types (int, at present) and the arrow *)
(* The types are too can be `read on-demand', that is, partly
   determined
*)
type base_t = Int
type tp_v = B of base_t | Arr of tp * tp
and  tp  = tp_v option -> tp_v
;;

(* Asserting the equality of two `tp' represented by `lazy generators' *)
let rec tp_same : tp -> tp -> unit = fun x y ->
  let _ = y (Some (x None)) in ()
and tp_v_same : tp_v -> tp_v -> unit = fun x y ->
  match (x,y) with
  | (B Int, B Int) -> ()
  | (Arr (t1o,t1a), Arr (t2o,t2a)) -> 
      tp_same t1o t2o; tp_same t1a t2a
  | _ -> fail ()
and tp_pure : tp_v -> tp = fun x -> function
  | None   -> x
  | Some y -> tp_v_same x y; y
;;

(* Convenient constructors *)
let int : tp = tp_pure (B Int);;
let arr : tp -> tp -> tp = fun t1 t2 -> tp_pure (Arr (t1,t2));;

(* Nice printing out of types, with no extra parentheses *)
let string_of_tp : tp -> string =
  let rec loop depth prec = function
    | B Int       -> "int"
    | Arr (t1,t2) -> if depth > 10 then "..." else paren (prec > 10) 
	              (loop (depth+1) 11 (t1 None) ^ " -> " ^ 
		       loop (depth+1) 10 (t2 None))
  in fun tp -> loop 0 0 (tp None)
;;


(* Lazy generator of types *)

open WorldLocalMem;;
let tp_memo : tp -> tp = fun tp ->
  let r = wref_new tp in
  fun x -> let tv = wref_get r x in
           wref_set (tp_pure tv) r; tv
;;


(* We don't bother to normalize probabilities; although it is quite easy *)

let a_tp : tp =
  let a_baset () = Int in	(* There is only one base type so far *)
  let rec loop = function
    | None -> dist [ (0.5, B (a_baset ()));
		     (0.5, Arr (tp_memo loop, tp_memo loop))]
    | Some tv -> tv
  in loop
;;

(* Test generating types and checking their equality *)
let [(0.5, "int"); (0.125, "int -> int")] =
run (Some 3) (fun () -> string_of_tp a_tp);;

let [(0.5, Ptypes.V _)] =
Inference.explore (Some 3) (reify0 (fun () -> tp_same a_tp int));;

let [(0.5, Ptypes.V _)] =
Inference.explore (Some 3) (reify0 (fun () -> 
  tp_same a_tp (arr int int)));;

(* Check memo *)
let [(0.6875, true)] =
run (Some 5) (fun () -> 
  let tp = tp_memo a_tp in
  (string_of_tp tp = string_of_tp tp))
;;

let [(0.03125, ("(int -> int) -> int", "(int -> int) -> int"));
     (0.125, ("int -> int", "int -> int"));
     (0.03125, ("int -> int -> int", "int -> int -> int"))] =
run (Some 5) (fun () -> 
  let tp = tp_memo a_tp in
  let tpa = arr (tp_memo a_tp) (tp_memo a_tp) in
  tp_same tp tpa;
  (string_of_tp tp, string_of_tp tpa))
;;

let [(0.1875, true)] =
run (Some 5) (fun () -> 
  let tp = tp_memo a_tp in
  let tpa = arr (tp_memo a_tp) (tp_memo a_tp) in
  tp_same tp tpa;
  tp_same tpa tp;
  (string_of_tp tp = string_of_tp tpa))
;;

let [(0.5, true)] =
run (Some 5) (fun () -> 
   let tpa = arr int (tp_memo a_tp) in
   let tpb = arr (tp_memo a_tp) (arr int int) in
  ignore (tp_same tpa tpb);
  (string_of_tp tpa = string_of_tp tpb))
;;

(* Infinite type: it is contractible *)
let [(0.5, ())] =
run (Some 5) (fun () -> 
   let tpa = tp_memo a_tp in
   let tpb = arr tpa int in
   tp_same tpa tpb
);;

let [] =
run None (fun () -> 
   let tpa = tp_memo a_tp in
   let tpb = arr tpa int in
   tp_same tpa tpb;
   tp_same int tpa
);;

(* Inference.explore (Some 10) (reify0 (fun () ->  *)
(*    let tpa = tp_memo a_tp in *)
(*    let tpb = arr tpa int in *)
(*    tp_same tpa (tp_same tpa tpb) *)
(* ));; *)

(* --- end of preliminaries --- *)

(* The type inference itself *)
type gamma = (varname * tp) list;;

let new_tvar () = tp_memo a_tp;;

let rec typeof : gamma -> term -> tp = fun gamma exp -> 
 match exp () with
  | I _    -> int
  | V name -> begin try List.assoc name gamma 
                    with Not_found -> fail () 
              end
  | L (v,body) ->
      let targ = new_tvar() in
      let tbody = typeof ((v,targ) :: gamma) body in
      arr targ tbody
   | A (e1,e2) ->
       let tres = new_tvar() in
       tp_same (typeof gamma e1) (arr (typeof gamma e2) tres);
       tres
;;

let do_infer bound term =
  run bound (fun () -> string_of_tp (typeof [] term))
;;

(* Examples of inferring types *)
(* For polymorphic types, we infer a stream of candidates *)
let [(0.03125, "((int -> int) -> int) -> int");
     (0.03125, "(int -> int -> int) -> int"); 
     (0.125, "(int -> int) -> int");
     (0.5, "int -> int")] =
do_infer (Some 4) (lam "f"  (num 1));;

let [] = do_infer None (lam "f" vx);;	(* unbound variable: ill-typed *)

let [(0.03125, "((int -> int) -> int) -> (int -> int) -> int");
     (0.03125, "(int -> int -> int) -> int -> int -> int");
     (0.125, "(int -> int) -> int -> int"); (0.5, "int -> int")] =
do_infer (Some 4) (lam "f" vf);;

let [(0.5, "int")] =
do_infer None ((lam "f" vf) % (num 1));;

let [(0.015625, "(int -> (int -> int) -> int) -> (int -> int) -> int");
     (0.015625, "(int -> int -> int -> int) -> int -> int -> int");
     (0.0625, "(int -> int -> int) -> int -> int");
     (0.25, "(int -> int) -> int")] =
do_infer (Some 5) (lam "f" (vf % num 1));;

do_infer (Some 3) (lam "x" (vx % vx));;	(* Alas, no occurs check *)

do_infer (Some 10) (lam "f" (lam "x" (vf % (vx % num 1))));;

let [] = 
do_infer None (lam "f" (lam "x" (vf % (vx % num 1) % (vx % lam "z" vz))));;


(* Generating well-typed terms *)
let [(0.1, ("1", "int")); 
     (0.00200000000000000048, ("Lx0. 1", "int -> int"))] =
run (Some 4) (fun () ->
  let term = a_term () in
  (string_of_term term, string_of_tp (typeof [] term)))
;;

let [(0.1, ("1", "int")); 
     (0.00200000000000000048, ("Lx0. 1", "int -> int"));
     (0.00180000000000000038, ("Lx1. 1", "int -> int"))] =
run (Some 5) (fun () ->
  let term = a_term () in
  (string_of_term term, string_of_tp (typeof [] term)))
;;

run (Some 7) (fun () ->
  let term = a_term () in
  (string_of_term term, string_of_tp (typeof [] term)))
;;

run (Some 9) (fun () ->
  let term = a_term () in
  (string_of_term term, string_of_tp (typeof [] term)))
;;

(* Generating sample int->int terms *)
run (Some 10) (fun () ->
  let term = a_term () in
  (string_of_term term, tp_same (arr int int) (typeof [] term)))
;;

(*
[(1.60000000000000077e-06, ("(Lx0. Lx0. 1) 1", ()));
 (1.60000000000000077e-06, ("Lx0. (Lx0. 1) 1", ()));
 (0.00200000000000000048, ("Lx0. 1", ()));
 (0.000200000000000000064, ("Lx0. x0", ()));
 (0.00180000000000000038, ("Lx1. 1", ()));
 (0.000162000000000000035, ("Lx1. x1", ()));
 (0.00162000000000000035, ("Lx2. 1", ()));
 (0.000131220000000000035, ("Lx2. x2", ()));
 (0.00145800000000000053, ("Lx3. 1", ()));
 (0.00131220000000000035, ("Lx4. 1", ()));
 (0.00118098000000000053, ("Lx5. 1", ()));
 (0.00106288200000000045, ("Lx6. 1", ()))]
*)

print_endline "\nAll done\n";;
