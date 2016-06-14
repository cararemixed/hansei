(* IBAL music evolution model: the warm-up

  Reproducing the non-recursive music.ibl in the MUSIC.NEW directory
  of IBAL.
  The result of IBAL sampling for 10 seconds, Intel(R) Xeon(TM) CPU 2.40GHz,
  512KB cache

./sample music.ibl 10
Number of samples = 109490
Probability of evidence = 0.0538844
"fsharp" : 0.008238
"b" : 0.138361
"c" : 0.499339
"e" : 0.008187
"f" : 0.007882
"g" : 0.002542
"csharp" : 0.335452

The gist of the IBAL code:

let transform(input) =
  if input |= []
  then []
  else 
    let f1 = 
      dist [ 0.5 : id, 
             0.2 : delete, 
             0.2 : maptranspose1, 
             0.1 : maptranspose5 ] in
    let f2 = 
      dist [ 0.5 : id, 
             0.2 : delete, 
             0.2 : maptranspose1, 
             0.1 : maptranspose5 ] in
    let z = split(input) in
    append(f1(z.fst), f2(z.snd))
in 

let x =
  observe ['asharp,_,_] in
  transform(['a,'b,'c])
in
x.CDR.CAR

*)

open Ptypes
open ProbM

(* Lazy Lists  *)
type 'a lcons = LNil | LCons of (unit -> 'a) * 'a llist
and  'a llist = unit -> 'a lcons
;;
let nil  = fun () -> LNil;;
let cons h t = fun () -> LCons (h,t);;

let rec lappend (y : 'a llist) (z : 'a llist) =
  letlazy (fun () -> 
  match y () with
  | LNil -> z ()
  | LCons (h,t) -> LCons (h, lappend t z));;

let lhead (x : 'a llist) = 
  match x () with LCons (h,_) -> h | LNil -> fail ()
;;

let ltail (x : 'a llist) = 
  match x () with LCons (_,t) -> t | LNil -> fail ()
;;

let rec to_lcons = function
  | [] -> nil
  | (h::t) -> cons (fun () -> h) (to_lcons t);;


let lreflect x = x ();;

let rec llength' = function
  | LNil -> 0
  | LCons (_,t) -> 1 + llength' (t ())
;;

let llength l = llength' (l ());;

let rec splitAt n lst =
  if n = 0 then (nil, lst)
  else 
    let LCons (h,t) = lst () in
    let (x1,x2) = splitAt (pred n) t in
    (cons h x1, x2)
;;

let split lst =
  let n = uniform (llength lst + 1) in
  splitAt n lst
;;

let rec lmap' f = function
  | LNil -> LNil
  | LCons (h,t) -> LCons (letlazy (fun () -> f (h ())), lmap f t)
and lmap f l = letlazy (fun () -> lmap' f (l ()))
;;


(* Notes and note transformations *)

type note = 
  A | Asharp | B | C | Csharp | D | Dsharp | E | F | Fsharp | G | Gsharp
;;

(* Transpose a note by 1 interval *)
let transpose1 = function
  | C      -> dist [ (0.3, Csharp); (0.6, D); (0.1, Dsharp) ]
  | Csharp -> dist [ (0.4, D); (0.6, Dsharp) ]
  | D      -> dist [ (0.3, Dsharp); (0.7, E) ]
  | Dsharp -> dist [ (0.7, E); (0.3, F) ]
  | E      -> dist [ (0.6, F); (0.4, Fsharp) ]
  | F      -> dist [ (0.3, Fsharp); (0.6, G); (0.1, Gsharp) ]
  | Fsharp -> dist [ (0.4, G); (0.6, Gsharp) ]
  | G      -> dist [ (0.3, Gsharp); (0.6, A); (0.1, Asharp) ]
  | Gsharp -> dist [ (0.4, A); (0.6, Asharp) ]
  | A      -> dist [ (0.3, Asharp); (0.7, B) ]
  | Asharp -> dist [ (0.7, B); (0.3, C) ]
  | B      -> dist [ (0.6, C); (0.4, Csharp) ]
;;

(* Transpose a note by 5 intervals *)
let transpose5 = function
  | C      -> dist [ (0.3, F); (0.1, Fsharp); (0.55, G); 
		     (0.05, Gsharp) ]
  | Csharp -> dist [ (0.3, Fsharp); (0.4, G); (0.3, Gsharp) ]
  | D      -> dist [ (0.3, G); (0.1, Gsharp); (0.55, A);
		     (0.05, Asharp) ]
  | Dsharp -> dist [ (0.3, Gsharp); (0.4, A); (0.3, Asharp) ]
  | E      -> dist [ (0.3, A); (0.1, Asharp); (0.55, B); (0.05, C) ]
  | F      -> dist [ (0.1, Asharp); (0.2, B); (0.6, C); (0.1, Csharp) ]
  | Fsharp -> dist [ (0.3, B); (0.4, C); (0.3, Csharp) ]
  | G      -> dist [ (0.3, C); (0.1, Csharp); (0.55, D); (0.05, Dsharp)]
  | Gsharp -> dist [ (0.3, Csharp); (0.4, D); (0.3, Dsharp) ]
  | A      -> dist [ (0.3, D); (0.1, Dsharp); (0.55, E); (0.05, F) ]
  | Asharp -> dist [ (0.3, Dsharp); (0.3, E); (0.4, F) ]
  | B      -> dist [ (0.3, E); (0.3, F); (0.3, Fsharp); (0.1, G) ]
;;

(* the main transformation *)

let transform x =
  match x () with
  | LNil -> nil
  | input ->
      let f1 = dist [ (0.5, fun x -> x);
		      (0.2, fun _ -> nil);
		      (0.2, lmap transpose1);
		      (0.1, lmap transpose5) ] in
      let f2 = dist [ (0.5, fun x -> x);
		      (0.2, fun _ -> nil);
		      (0.2, lmap transpose1);
		      (0.1, lmap transpose5) ] in
      let (z1,z2) = split (fun () -> input) in
      lappend (f1 z1) (f2 z2)
;;

(* The main functon *)
let main () =
  let input = to_lcons [A;B;C] in
  let x = transform input in
  let () = if not (llength x = 3 && lreflect (lhead x) = Asharp) then fail () in
  lreflect(lhead (ltail x))
;;

(* We got the exact result! *)
let r =  exact_reify main;;
(* reify: done; 29 accepted 106 rejected 0 left *)
let () = assert (r =
   [(0.000150000000000000041, V G); (0.000450000000000000042, V Fsharp);
    (0.000450000000000000042, V F); (0.000450000000000000042, V E);
    (0.018, V Csharp); (0.0270000000000000032, V C); (0.0075, V B)]);;
let evidence_p = List.fold_left (fun z (p,_) -> z +. p) 0. r;;
let () = assert(
 evidence_p = 0.054);;

(* Normalized answer: matches very well with that computed by IBAL.
   It took hardly any time on our system, and the asnwer is exact.
*)
let () = assert(
  List.map (fun (p,e) -> (p /. evidence_p, e)) r
 =
[(0.00277777777777777875, V G); (0.00833333333333333495, V Fsharp);
 (0.00833333333333333495, V F); (0.00833333333333333495, V E);
 (0.333333333333333315, V Csharp); (0.500000000000000111, V C);
 (0.138888888888888895, V B)]);;

(* For comparison, we use sampling, too *)

(* 1000 samples is quite good, actually *)
let
[(0.000202499999999999962, V G); (0.000607499999999999859, V Fsharp);
 (0.000607499999999999859, V F); (0.000607499999999999859, V E);
 (0.0179820000000001541, V Csharp); (0.0269730000000001947, V C);
 (0.00785700000000001848, V B)]
    =  sample_importance (random_selector 17) 1000 main;;

let evidence_p = List.fold_left (fun z (p,_) -> z +. p) 0. r;;
let () = assert(
 evidence_p = 0.054);;

(* The result is actually exact.
The exact is 0.054. IBAL computed 0.0538844 with 100 times more
samples.
*)
