(* Probabilistic embedded domain specific language *)

(* Tests of rejection and importance sampling *)

open Ptypes
open ProbM;;


(* ------------------------------------------------------------------------
 * Basic tests, approximate sampling
 *)

let tflip2_shared () =   (* sharing of flips *)
  let v = flip 0.5 in
  v && v;;
let () = assert (
  sample_rejection (random_selector 1) 100 tflip2_shared
    = [(0.48, V true); (0.52, V false)]);;
let () = assert (
  sample_importance (random_selector 1) 100 tflip2_shared
    = [(0.5, V true); (0.5, V false)]);;

let tflip2_noshared () =   (* independent flips *)
  flip 0.5 && flip 0.5;;
let () = assert (
  sample_rejection (random_selector 1) 100 tflip2_noshared
    = [(0.24, V true); (0.76, V false)]);;
let () = assert (
  sample_importance (random_selector 1) 100 tflip2_noshared
    = [(0.25, V true); (0.75, V false)]);;

let talarm () =
  let earthquake = flip 0.01 and burglary = flip 0.1 in
  if earthquake 
     then if burglary then flip 0.99 else flip 0.2
     else if burglary then flip 0.98 else flip 0.01
;;
let () = assert (
  sample_rejection (random_selector 1) 100 talarm
  = [(0.14, V true); (0.86, V false)]);;
let () = assert (
  sample_importance (random_selector 1) 100 talarm
  = [(0.108720000000000011, V true); (0.891280000000000072, V false)]);;
(* old result:
  = [(0.106999999999999929, V true); (0.892999999999999, V false)]);;
*)
(* exact result:
  = PV [(0.108720000000000011, V true); (0.891280000000000072, V false)])
*)

(* Tests of library distributions *)

(* exact result:
    n = 0: 0.85
    n = 1: 0.85 *. 0.15         = 0.1275
    n = 2: 0.85 *. (0.15 ** 2.) = 0.019125
    n = 3: 0.85 *. (0.15 ** 3.) = 0.00286874999999999934
    n = 4: 0.85 *. (0.15 ** 4.) = 0.0004303125
    n = 5: 0.85 *. (0.15 ** 5.) = 6.45468749999999884e-05
*)

(* Rejection sampling *)
let [(0.04, V 2); (0.17, V 1); (0.79, V 0)] =
    sample_rejection (random_selector 17) 100 (fun () -> geometric 0.85);;

(* Our importance sampling *)
let [(0.000450000000000000096, V 4); (0.00247500000000000107, V 3);
   (0.0195749999999999813, V 2); (0.1275, V 1); (0.85, V 0)] =
  sample_importance (random_selector 17) 100 (fun () -> geometric 0.85);;

let [(2.25000000000000048e-05, V 6); (9.00000000000000192e-05, V 5);
   (0.000472500000000000318, V 4); (0.00283499999999999681, V 3);
   (0.0190800000000004057, V 2); (0.1275, V 1); (0.85, V 0)] =
  sample_importance (random_selector 17) 1000 (fun () -> geometric 0.85);;


(* Geometric-bounded is a very specific case: the search tree can be
   explored in constant memory, with a jobqueue of size 1.
*)
let (0.999494006159381776, 0.999494006159381776) =
Inference.bounded_explore 1
    (reify0 (fun () -> if geometric_bounded 7 0.85 > 3 then fail ()));;

(* ------------------------------------------------------------------------
 * Baseline, approximate sampling, rejection sampling
 *)

(* foo.ibl, program 3
  //P(e) = 0.25; P(T) = 1.0
 obs true in
   ({ f = if dist [ 0.1 : true, 0.9 : false ]
          then dist [ 0.7 : 'a, 0.3 : 'b ]
          else dist [ 0.2 : 'a, 0.8 : 'b ],
      g = 'c }).f
   == 'a
*)
let tfooibl3 () = 
  observe (fun x -> x = true) (fun () ->
  (object
    method mf = if dist [ (0.1, true); (0.9, false) ]
                then dist [ (0.7, 'a'); (0.3, 'b') ]
                else dist [ (0.2, 'a'); (0.8, 'b') ]
    method mg = 'c' end)#mf
   = 'a');;

let () = assert (
          sample_importance (random_selector 1) 100 tfooibl3
    = [(0.25, V true)]);;

(* exact result: PV [(0.25, V true)] *)

(* test2.ibl
let x = 
  obs { z : 'a } in 
  dist [ 0.01 : { z = 'a, w = 'b }, 
         0.02 : { z = 'a, w = 'c },
         0.97 : { z = 'd, w = 'e } ]
in
let y = 
  if x.w == 'b 
  then dist [ 0.9 : true, 0.1 : false ]
  else if x.w == 'c
  then dist [ 0.6 : true, 0.4 : false ]
  else dist [ 0.2 : true, 0.8 : false ]
in
y
*)

let tiblt2 () = 
  let x = 
    observe (fun r -> r#mz = 'a') (fun () ->
      dist [ (0.01, object method mz = 'a' method mw = 'b' end);
             (0.02, object method mz = 'a' method mw = 'c' end);
             (0.97, object method mz = 'd' method mw = 'e' end) ])
  in
  let y = 
    if x#mw = 'b'
    then dist [ (0.9, true); (0.1, false) ]
    else if x#mw = 'c'
    then dist [ (0.6, true); (0.4, false) ]
    else dist [ (0.2, true); (0.8, false) ]
in y;;

(* Naive rejection sampling is hopeless *)
let () = assert (
          sample_rejection (random_selector 1) 100 tiblt2
 = [(0.02, V false)]);;

(* Our look-ahead sampling gives quite a precise result even with 100 samples *)
let () = assert (
          sample_importance (random_selector 1) 100 tiblt2
 = [(0.021, V true); (0.00900000000000000105, V false)]);;

(* exact:  PV [(0.021, V true); (0.00900000000000000105, V false)] *)


(* test from the Music TR, Chap 4
 let f() = dist [ 0.1 : true, 0.9 : false ] in
 let g() = dist [ 0.3 : true, 0.7 : false ] in
 observe true in
 dist [ 0.8 : f(), 0.2 : g() ]
*)

let tmusictr41 () = 
 let f () = flip 0.1 in
 let g () = flip 0.3 in
 observe (fun x -> x = true) (fun () ->
 dist [ (0.8, f ()); (0.2, g ()) ]);;

let () = assert (
          sample_importance (random_selector 1) 100  tmusictr41
    = [(0.14, V true)]);;
(* old   = [(0.17, V true)]);; *)
(* exact result:
    = PV [(0.14, V true)]);;
*)

(* test from the Music TR, Chap 4
 let f() = dist [ 0.01 : true, 0.99 : false ] in
 (observe { p : 'a } in
 if f()
 then { p = 'a, q = dist [ 0.3 : true,
                          0.7 : false ] }
 else { p = 'b, q = true }).q
*)

let tmusictr42 () = 
 let f () = flip 0.01 in
 (observe (fun r -> r#mp = 'a') (fun () ->
   if f ()
   then object method mp = 'a'
               method mq = flip 0.3 end
   else object method mp = 'b' method mq = true end))#mq;;

(* Clear evidence why rejection sample doesn't often work *)
(* It used to be a clear evidence. The look-ahead helps: even with
   10 samples we get almost exact result.
   Now, with shallow initial exploration, the result is exact.
*)
let () = assert (
          sample_importance (random_selector 1) 1 tmusictr42
  = [(0.003, V true); (0.00699999999999999928, V false)]);;

(* exact result
    = PV [(0.003, V true); (0.00699999999999999928, V false)]);;
*)

(* ------------------------------------------------------------------------
 * Importance sampling by evidence lookahead
 * very large depth and very low probability of acceptance
 *)

(* Drunken coin example: coin flipping by a drunk. 
   Because the person flipping the coin is drunk, most of the time
   the result of flipping is a lost/dropped coin
*)

(* The following is too easy 
let drunk_coin () = 
  dist [ (0.9, V fail);
	 (0.1, V (fun () -> flip 0.5))] ();;
*)

let drunk_coin () = 
  let x = flip 0.5 in
  let lost = flip 0.9 in
  if lost then fail () else x;;

(* Compute AND of n tosses of the drunk coin *)
let rec dcoin_and = function
  | 1 -> drunk_coin ()
  | n -> drunk_coin () && dcoin_and (n-1)
;;

(* Exact probability *)
let () = assert (
  exact_reify (fun () -> dcoin_and 10)
 = [(9.76562499999997764e-14, V true); (0.0526315789473632695, V false)]);;
(* reify: done; 11 accepted 10 rejected 0 left *)
(* Thus we managed to do with only 21 threads *)


(* Pure rejection sample *)
let () = assert (
  sample_rejection (random_selector 17) 100 (fun () -> dcoin_and 10)
  = [(0.05, V false)]);;

let () = assert (
  sample_rejection (random_selector 17) 10000 (fun () -> dcoin_and 10)
  = [(0.0514, V false)]);;

(* Using our look-ahead sampling *)
let () = assert (
  sample_importance (random_selector 17) 100 (fun () -> dcoin_and 10)
 = [(0.052301965599999993, V false)]);;
(* without pre-exploration:
 = [(0.0485964009999999488, V false)]);;
*)

let () = assert (
  sample_importance (random_selector 1) 5000 (fun () -> dcoin_and 10)
 = [(6.99999999999998406e-14, V true); (0.0526354788429301348, V false)]);;
(* without pre-exploration:
 = [(1.19999999999999741e-13, V true); (0.0527161389576979306, V false)]);;
*)

let () = assert (
  sample_importance (random_selector 17) 5000 (fun () -> dcoin_and 10)
 = [(5.99999999999998706e-14, V true); (0.0526415594361701461, V false)]);;
(* without pre-exploration:
 = [(1.19999999999999741e-13, V true); (0.0523119433654579066, V false)]);;
*)

(* Statistics of sampling *)
let test_errors f =
  List.map
  (fun nsamples -> 
    (nsamples,
     Inference.statistics (1,50) 
       (fun randomseed -> 
	 sample_importance (random_selector randomseed) nsamples 
	   (fun () -> f 10))))
  [100;200;300;400;500;600;700];;

(*
test_errors dcoin_and;;
- : (int * (bool * float * float) list) list =
With pre-exploration (shallow exploration at the start of sampling):
[(100,
  [(true, 1.29999999999999724e-13, 2.60959767013997198e-13);
   (false, 0.05265430071828, 0.000249859489942825521)]);
 (200,
  [(true, 1.09999999999999721e-13, 1.74355957741626505e-13);
   (false, 0.052632157955119975, 0.000186412392645234363)]);
 (300,
  [(true, 1.23333333333332976e-13, 1.36666666666666421e-13);
   (false, 0.0526383685437966514, 0.000133601765164043519)]);
 (400,
  [(true, 1.19999999999999691e-13, 1.11691539518443132e-13);
   (false, 0.0526302288048175, 0.000117820911159147759)]);
 (500,
  [(true, 1.0799999999999978e-13, 1.01666120217110414e-13);
   (false, 0.0526402060049079579, 9.68941357687236402e-05)]);
 (600,
  [(true, 9.99999999999997506e-14, 9.27960727138335121e-14);
   (false, 0.0526366372010099587, 8.53853249567030763e-05)]);
 (700,
  [(true, 9.85714285714283083e-14, 8.43825110035561582e-14);
   (false, 0.0526417155630785408, 9.20480236531866247e-05)])]

Without pre-exploration:
[(100,
  [(true, 7.99999999999998232e-14, 2.71293199325010147e-13);
   (false, 0.0531157451526199434, 0.00478993009145036158)]);
 (200,
  [(true, 9.99999999999998e-14, 2.64575131106458452e-13);
   (false, 0.053025832461059845, 0.00349750459271379538)]);
 (300,
  [(true, 7.33333333333331765e-14, 1.91949067318505837e-13);
   (false, 0.0529673570300064692, 0.00293091296491828322)]);
 (400,
  [(true, 7.99999999999998232e-14, 1.61554944214034772e-13);
   (false, 0.0528950958928401244, 0.00259528736219077688)]);
 (500,
  [(true, 7.99999999999998232e-14, 1.32664991614215687e-13);
   (false, 0.0527723947097123516, 0.00227511514422131227)]);
 (600,
  [(true, 8.33333333333331465e-14, 1.25830573921178876e-13);
   (false, 0.0529748641834071679, 0.00212307278193318502)]);
 (700,
  [(true, 7.71428571428569512e-14, 1.11428571428571188e-13);
   (false, 0.0528989027528804709, 0.00192805251823919611)])]

Obviously, pre-exploration decreases the standard deviation.
*)

(* Look ahead by more than one step *)
(* This is obsolete; this sort of memoization does not scale to larger problems
(* The look-ahead depth 0 corresponds to sample_explore
let () = assert (
  sample_explore_reify 1 100 0 (fun () -> dcoin_and 10)
  = [(9.99999999999997758e-13, V true); (0.0564262019999999462, V false)]);;

(* That is essentially the exact result! *)
let () = assert (
  sample_explore_reify 17 100 1 (fun () -> dcoin_and 10)
  = [(9.76562499999997385e-14, V true); (0.052631578947363318, V false)]);;

let () = assert (
  sample_explore_reify 1 100 2 (fun () -> dcoin_and 10)
  = [(9.76562499999997259e-14, V true); (0.052631578947362978, V false)]);;
*)


(* xxx lines printed *)
(*
reify: done; 0 accepted 1 rejected 2 left
reify: done; 0 accepted 1 rejected 2 left
reify: finished deterministically
reify: done; 0 accepted 1 rejected 2 left
reify: finished deterministically
reify: done; 0 accepted 1 rejected 2 left
reify: finished deterministically
reify: finished deterministically
...
*)

(*
let () = assert (
  sample_explore_reify_memoize 1 100 2 (fun () -> dcoin_and 10)
 = [(8.59374999999998168e-14, V true); (0.0529157894736801901, V false)]);;
*)

(* Now, we get the same result as before, only _much_ faster

reify: done; 0 accepted 1 rejected 2 left
reify: done; 0 accepted 1 rejected 2 left
reify: finished deterministically
reify: finished deterministically
reify: done; 0 accepted 1 rejected 2 left
reify: done; 0 accepted 1 rejected 2 left
reify: finished deterministically
reify: finished deterministically
reify: done; 0 accepted 1 rejected 2 left
reify: finished deterministically
reify: done; 0 accepted 1 rejected 2 left
reify: done; 0 accepted 1 rejected 2 left
reify: done; 0 accepted 1 rejected 2 left
reify: finished deterministically

Instead of 168 lines printed, only 14 are printed. Only 14 worlds are explored.
The sampling result is identical to that without memoization.
*)
*)

let dcoin_and_true n = dcoin_and n || fail ();;

(* Rejection sampling is hopeless *)
let () = assert (
  sample_rejection (random_selector 1) 10000 (fun () -> dcoin_and_true 10)
 = []);;

(* Memoization does help! The result is essentially exact; with only 100 samples
*)
(*
let () = assert (
  sample_importance (random_selector 1) 100 (fun () -> dcoin_and_true 10)
 = [(4.99999999999998879e-13, V true)]);;
(* was with sample_explore_reify_memoize, depth 2.
 = [(8.59374999999998168e-14, V true)]);;
*)
*)

(* Statistics of sampling *)
(*
let test_errors nsamples f =
  List.map
    (fun maxdepth -> maxdepth,
      statistics (1,50) 
	(fun randomseed -> 
	  sample_importance (random_selector randomseed)
	    nsamples maxdepth (fun () -> f 10)))
    [0;1;2;3;4;5;6;7;8];;
*)
(*
test_errors 100 dcoin_and;;
[(0,
  [(true, 7.99999999999998232e-14, 2.71293199325010147e-13);
   (false, 0.0531157451526199434, 0.00478993009145036158)]);
 (1,
  [(true, 9.76562499999997764e-14, nan);
   (false, 0.0526315789473632903, 1.49011611938476571e-09)]);
 (2,
  [(true, 9.78515624999998e-14, 9.11295558381908359e-15);
   (false, 0.0526268421052586, 0.000221013154368397181)]);
 (3,
  [(true, 9.76562499999997764e-14, nan);
   (false, 0.0526315789473629711, 1.49011611938476571e-09)]);
 (4,
  [(true, 9.4335937499999755e-14, 1.08762935877549113e-14);
   (false, 0.0526356052631531193, 1.31889370669237678e-05)]);
 (5,
  [(true, 9.76562499999997764e-14, nan); (false, 0.0526315789473626311, nan)]);
 (6,
  [(true, 9.76171874999998073e-14, 8.70392795331e-15);
   (false, 0.0526315813157843745, 5.27734674452341682e-07)]);
 (7,
  [(true, 9.76562499999997764e-14, nan);
   (false, 0.0526315789473637344, 2.23517417907714835e-09)]);
 (8,
  [(true, 9.69140624999998e-14, 9.50343341019619687e-15);
   (false, 0.0526315811973636, 2.88078411358314818e-08)])]

test_errors 100 dcoin_and_true;;
[(0, [(true, 7.99999999999998232e-14, 2.71293199325010147e-13)]);
 (1, [(true, 9.76562499999997764e-14, nan)]);
 (2, [(true, 9.78515624999998e-14, 9.11295558381908359e-15)]);
 (3, [(true, 9.76562499999997764e-14, nan)]);
 (4, [(true, 9.76171874999998073e-14, 8.70392795331e-15)]);
 (5, [(true, 9.76562499999997764e-14, nan)]);
 (6, [(true, 9.69140624999998213e-14, 9.50343341019600439e-15)]);
 (7, [(true, 9.76562499999997764e-14, nan)]);
 (8, [(true, 9.69140624999998213e-14, 9.50343341019600439e-15)])]
*)

Inference.bounded_explore 1
    (reify0 (fun () -> if not (dcoin_and 10) then fail ()));;

let (0., 1.) =
Inference.bounded_explore 1
    (reify0 (fun () -> if not (dcoin_and 10) then fail ()));;

let (0., 0.0499999999999999889) =
Inference.bounded_explore 3
    (reify0 (fun () -> if not (dcoin_and 10) then fail ()));;

(* Exact result is achieved *)
let (9.76562499999997764e-14, 9.76562499999997764e-14) =
Inference.bounded_explore 5
    (reify0 (fun () -> if not (dcoin_and 10) then fail ()));;
