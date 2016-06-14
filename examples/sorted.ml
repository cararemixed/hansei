(* Solving the problem proposed by Georges Harik:

   We draw a list of size n of independent random numbers,
   uniformly distributed in the interval 0..m-1.
   We should estimate the probability of the list being sorted.
   For large m (when duplicates are unlikely), the theoretical
   probability is about 1/n!

   The problem is especially interesting when m is about 10^6 and n
   is about 50-100.
*)

(* Open the Hansei library *)
open Ptypes
open ProbM
;;

(* Lazy Lists  *)
type 'a lcons = LNil | LCons of 'a * 'a llist
and  'a llist = unit -> 'a lcons
;;

(* Generate a random list of size n whose elements are the results
   of evaluating the thunk. The thunk may be a non-deterministic
   computation, so the elements of the list are not necessarily the same.
   The letlazy below is a memoization higher-order function.
*)
let rec build_list n thunk () = 
  if n = 0 then LNil
  else LCons (thunk (), letlazy (build_list (pred n) thunk))
;;

(* Convert a lazy list to the ordinary list, so we can print it out *)
let rec to_list l = match l () with
 |  LNil        -> []
 |  LCons (d,l) -> d::to_list l;;

(* Test to see that a lazy list l is sorted given the ordering predicate
   gte: gte x y returns true if x >= y
*)
let is_sorted gte (l : 'a llist) = 
  let rec loop xprev = function
    | LNil        -> true
    | LCons (x,l) -> gte x xprev && loop x (l ())
  in match l () with
  | LNil        -> true
  | LCons (x,l) -> loop x (l ())
;;

(* We use lazy lists of bits (most significant bit first) to 
   represent the numbers *)

(* Generate a random list of bits of size d *)
let bit_list d : int llist = 
  letlazy (build_list d (fun () -> dist [(0.5,0);(0.5,1)]));;

(* Test the distribution of bit lists of size 4:
   the sampled lists should be uniformly distributed *)
(* The following is the regression test. If the result of the
   exact_reify expression differs from the pattern on the 
   left-hand-side of let, error will be signaled.
*)

let [(0.0625, V [1; 1; 1; 1]); (0.0625, V [1; 1; 1; 0]);
   (0.0625, V [1; 1; 0; 1]); (0.0625, V [1; 1; 0; 0]);
   (0.0625, V [1; 0; 1; 1]); (0.0625, V [1; 0; 1; 0]);
   (0.0625, V [1; 0; 0; 1]); (0.0625, V [1; 0; 0; 0]);
   (0.0625, V [0; 1; 1; 1]); (0.0625, V [0; 1; 1; 0]);
   (0.0625, V [0; 1; 0; 1]); (0.0625, V [0; 1; 0; 0]);
   (0.0625, V [0; 0; 1; 1]); (0.0625, V [0; 0; 1; 0]);
   (0.0625, V [0; 0; 0; 1]); (0.0625, V [0; 0; 0; 0])]
 = exact_reify (fun () -> to_list (bit_list 4));;

(* Testing laziness. The two evaluations of (to_list l) below
   must return identical values, even though l is non-deterministic.
*)

let [(0.125, V ([1; 1; 1], [1; 1; 1])); (0.125, V ([1; 1; 0], [1; 1; 0]));
     (0.125, V ([1; 0; 1], [1; 0; 1])); (0.125, V ([1; 0; 0], [1; 0; 0]));
     (0.125, V ([0; 1; 1], [0; 1; 1])); (0.125, V ([0; 1; 0], [0; 1; 0]));
     (0.125, V ([0; 0; 1], [0; 0; 1])); (0.125, V ([0; 0; 0], [0; 0; 0]))]
 = exact_reify (fun () ->
 let l = bit_list 3 in (to_list l, to_list l));;

(* The order predicate of numbers represented as big-endian bit strings 
   of equal length
*)
let rec gte l1 l2 = match (l1 (), l2 ()) with
| (LNil,LNil) -> true
| (LNil,_)    -> false
| (_,LNil)    -> true
| (LCons (1,_),  LCons (0,_))  -> true
| (LCons (0,_),  LCons (1,_))  -> false
| (LCons (_,l1), LCons (_,l2)) ->  gte l1 l2;;

(* Testing gte *)
(* 10/16 of the samples should come true. Indeed: *)
let [(0.625, V true); (0.375, V false)] = 
exact_reify (fun () -> 
 let l1 = bit_list 2 in
 let l2 = bit_list 2 in
 gte l1 l2);;

(* 36/64 = 0.5625 should come true *)
let [(0.5625, V true); (0.4375, V false)] = 
exact_reify (fun () -> 
 let l1 = bit_list 3 in
 let l2 = bit_list 3 in
 gte l1 l2);;

(* Build the list of n elements, where each element is a random
   bit string of size d.
*)
let rec num_list n d = build_list n (fun () -> bit_list d);;

(* Here is our probabilistic model; each drawn
   number is independently uniformly distributed
   in 0 .. 2^20 (about 10^6) *)
let model n () =
  let l = num_list n 20 in
  if is_sorted gte l then () else fail ()
;;

(*
exact_reify (fun () -> is_sorted (>=) 
 (build_list 4 (fun () -> uniform 8)));;
*)


(* Preliminary tests, reproducing the earlier results. *)
let [(0.625, V true); (0.375, V false)] = 
exact_reify (fun () -> is_sorted gte (num_list 2 2));;

let [(0.5625, V true); (0.4375, V false)] = 
exact_reify (fun () -> is_sorted gte (num_list 2 3));;

let [(0.234375, V true); (0.765625, V false)] = 
exact_reify (fun () -> is_sorted gte (num_list 3 3));;
(* The exact result is computed as follows *)

let rec sum n m body = 
 if n = m then body n else
 if n > m then 0 else
 body n + sum (succ n) m body
;;
let testp3_theory = 
  float_of_int (sum 0 7 (fun i -> sum i 7 (fun j -> sum j 7 (fun k -> 1)))) /.
  float_of_int (64*8);;
(*
val testp3_theory : float = 0.234375
*)

let [(0.08056640625, V true); (0.91943359375, V false)] = 
exact_reify (fun () -> is_sorted gte (num_list 4 3));;
let testp4_theory = 
 float_of_int
  (sum 0 7 (fun i0 ->
   sum i0 7 (fun i -> sum i 7 (fun j -> sum j 7 (fun k -> 1))))) /.
  float_of_int (64 * 64);;
(*
val testp4_theory : float = 0.08056640625
*)

let [(0.04993438720703125, V true); (0.95006561279296875, V false)] = 
exact_reify (fun () -> is_sorted gte (num_list 4 5));;
let testp5_theory = 
 float_of_int
  (sum 0 31 (fun i0 ->
   sum i0 31 (fun i -> sum i 31 (fun j -> sum j 31 (fun k -> 1))))) /.
  float_of_int (32 * 32 * 32 * 32);;
(*
  val testp5_theory : float = 0.04993438720703125
*)

(* Now check how importance sampling works on the same examples.
   We try 100 and 200 samples, to see the convergence. *)
let [(0.04451904296875, V true); (0.95548095703125, V false)] = 
sample_importance (random_selector 17) 100 
    (fun () -> is_sorted gte (num_list 4 5));;

let [(0.05048828125, V true); (0.94951171875, V false)] = 
sample_importance (random_selector 17) 200 
    (fun () -> is_sorted gte (num_list 4 5));;

(* We now use the full model *)
let rec invfact n = 
  if n = 0 then 1. else invfact (pred n) /. float_of_int n;;

let [(0.507880630493164, V ())] = 
sample_importance (random_selector 17) 100 (model 2);;

(* Lists of size 3 (each element is uniform 2^20) *)
(* invfact 3 is 0.166666666666666657 *)
let [(0.181672331919253333, V ())] = 
sample_importance (random_selector 17) 100 (model 3);;


(* Lists of size 4 (each element is uniform 2^20) *)
(* invfact 4 is 0.0416666666666666644 *)
let [(0.0409626036065674284, V ())] = 
sample_importance (random_selector 17) 200 (model 4);;

(* Lists of size 5 (each element is uniform 2^20) 
   We try several sample sizes: 200, 400, 800, 1600. *)
let test = Inference.timeit
(fun () -> sample_importance (random_selector 17) 200 (model 5));;
(*
Time spent: 0.844053 sec
val test : unit Ptypes.pV = [(0.00738026769254247501, V ())]
*)
(* 1/120! is 0.00833333333333333322 *)

let test = Inference.timeit
(fun () -> sample_importance (random_selector 17) 400 (model 5));;
(*
Time spent: 1.71211 sec
val test : unit Ptypes.pV = [(0.00697125234993052362, V ())]
*)
let test = Inference.timeit
(fun () -> sample_importance (random_selector 17) 800 (model 5));;
(*
Time spent: 3.39221 sec
val test : unit Ptypes.pV = [(0.00813329801447366593, V ())]
*)
let test = Inference.timeit
(fun () -> sample_importance (random_selector 17) 1600 (model 5));;
(*
Time spent: 6.75242 sec
val test : unit Ptypes.pV = [(0.00845815535276950303, V ())]
*)


(* Lists of size 10 (each element is uniform 2^20) 
   We try several sample sizes.

   invfact 10 is 2.75573192239858883e-07
*)

let test = Inference.timeit
(fun () -> sample_importance (random_selector 17) 1000 (model 10));;
(*
Time spent: 8.0325 sec, on Asus EeePC 701
val test : unit Ptypes.pV = [(1.69135798502958471e-07, V ())]
*)
let test = Inference.timeit
(fun () -> sample_importance (random_selector 17) 2000 (model 10));;
(*
Time spent: 16.009 sec, on Asus EeePC 701
val test : unit Ptypes.pV = [(1.83189250977364207e-07, V ())]
*)
let test = Inference.timeit
(fun () -> sample_importance (random_selector 17) 4000 (model 10));;
(*
Time spent: 31.99 sec, on Asus EeePC 701
val test : unit Ptypes.pV = [(1.82758496998557692e-07, V ())]
*)
let test = Inference.timeit
(fun () -> sample_importance (random_selector 17) 8000 (model 10));;
(*
Time spent: 63.924 sec, on Asus EeePC 701
val test : unit Ptypes.pV = [(2.22648033692320351e-07, V ())]
*)

(* Lists of size 20 (each element is uniform 2^20) 
   We try several sample sizes.

invfact 20 is 4.11031762331216533e-19
*)

let test = Inference.timeit
(fun () -> sample_importance (random_selector 17) 8000 (model 20));;
(*
Time spent: 155.922 sec, on Asus EeePC 701
val test : unit Ptypes.pV = [(9.57988821435764199e-22, V ())]
*)
let test = Inference.timeit
(fun () -> sample_importance (random_selector 17) 24000 (model 20));;
(*
Time spent: 467.441 sec, on Asus EeePC 701
val test : unit Ptypes.pV = [(3.63611034052530686e-20, V ())]
*)
