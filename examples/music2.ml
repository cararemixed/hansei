(* IBAL music evolution model.

  Reproducing the recursive music.src1.dst1.ibl and
  music.src1.dst7.ibl in the MUSIC.NEW directory
  of IBAL.
  The result of IBAL sampling for 10 seconds, Intel(R) Xeon(TM) CPU 2.40GHz,
  512KB cache

~> ./sample music.src1.dst1.ibl 10
Number of samples = 28434
Probability of evidence = 2.81353e-07
{TAG : "CONS", CAR : "e", CDR : {TAG : "CONS", CAR : "d", CDR : {TAG : "CONS", CAR : "c", CDR : {TAG : "CONS", CAR : "b", CDR : {TAG : "CONS", CAR : "a", CDR : {TAG : "CONS", CAR : "b", CDR : {TAG : "NIL"}}}}}}} : 1.000000

~> ./sample music.src1.dst1.ibl 20
Number of samples = 56183
Probability of evidence = 4.51685e-07

~> ./sample music.src1.dst1.ibl 40
Number of samples = 113415
Probability of evidence = 4.72248e-07

The gist of the IBAL code:

let transform(input) =
  let maptranspose2(list) = transform(map(transpose2,list)) in
  let maptranspose3(list) = transform(map(transpose3,list)) in
  let maptranspose4(list) = transform(map(transpose4,list)) in
  let maptranspose5(list) = transform(map(transpose5,list)) in
  let maptranspose6(list) = transform(map(transpose6,list)) in
  let maptranspose7(list) = transform(map(transpose7,list)) in
  let delete(list) = [] in
  let id(list) = list in

  let chooseOp () =
    dist [ 0.4 : id, 
           0.2 : delete, 
           0.1 : maptranspose2, 
	   0.05 : maptranspose3,
	   0.05 : maptranspose4,
           0.05 : maptranspose5,
           0.05 : maptranspose6,
           0.1 : maptranspose7 ] in

  if input |= []
  then []
  else 
    let f1 = chooseOp() in
    let f2 = chooseOp() in
    let z = split(input) in
    append(f1(z.fst), f2(z.snd))
in 

let x =
  observe ['e, 'd, 'c, 'b, 'a, 'b] in
  transform(['e, 'a, 'c, 'e, 'a, 'c, 'b, 'a, 'gsharp, 'a])
in
x

The dst7 code has a different observation.
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

(* Compare a lazy list with a real one *)
let rec lobserve ll l = 
  match (ll (), l) with
  | (LNil,[]) -> ()
  | (LCons (h1,t1), (h2::t2)) -> if h1 () = h2 then lobserve t1 t2
	                            else fail ()
  | _ -> fail ()
;;


(* Notes and note transformations *)
(* Compared to IBAL, we are able to  express the transformations much more
   concisely, thank to the richness of the host language.
*)

type note = 
  A | Asharp | B | C | Csharp | D | Dsharp | E | F | Fsharp | G | Gsharp
;;

let octave  = [A; Asharp; B; C; Csharp; D; Dsharp; E; F; Fsharp; G; Gsharp;
	       A; Asharp; B; C; Csharp; D; Dsharp; E; F; Fsharp; G; Gsharp;
	       A; Asharp; B; C; Csharp; D; Dsharp; E; F; Fsharp; G; Gsharp];;

let note_to_int = function
  | A      -> 0
  | Asharp -> 1
  | B      -> 2
  | C      -> 3
  | Csharp -> 4
  | D      -> 5
  | Dsharp -> 6
  | E      -> 7
  | F      -> 8
  | Fsharp -> 9
  | G      -> 10
  | Gsharp -> 11
;;


let rec transp probs octave =
  match (probs,octave) with
  | ([],_) -> []
  | ((p::pt),(n::nt)) -> (p, n) :: transp pt nt
;;

let rec drop n l = match (n,l) with
| (0,l) -> l
| (n,_::l) -> drop (pred n) l
;;

let transpose probs n = 
  let arr = Array.init 12 (fun i -> transp probs (drop (n+i)  octave)) in
  fun note -> dist (arr.(note_to_int note))
;;

(* pre-compute the transformations *)
let transpose2 = transpose [0.4;0.5;0.1] 1
and transpose3 = transpose [0.1;0.4;0.4;0.1] 2
and transpose4 = transpose [0.1;0.5;0.3;0.1] 4
and transpose5 = transpose [0.1;0.3;0.5;0.1] 5
and transpose6 = transpose [0.1;0.4;0.4;0.1] 7
and transpose7 = transpose [0.1;0.5;0.4] 9
;;


(* the main transformation *)

let rec maptranspose2 l = transform(lmap transpose2 l)
and     maptranspose3 l = transform(lmap transpose3 l)
and     maptranspose4 l = transform(lmap transpose4 l)
and     maptranspose5 l = transform(lmap transpose5 l)
and     maptranspose6 l = transform(lmap transpose6 l)
and     maptranspose7 l = transform(lmap transpose7 l)
and id l = l
and delete l = nil
and choose_op () =
    dist [ (0.4, id);
           (0.2, delete);
           (0.1, maptranspose2);
           (0.05, maptranspose3);
           (0.05, maptranspose4);
           (0.05, maptranspose5);
           (0.05, maptranspose6);
           (0.1,  maptranspose7) ]
and transform x =
  match x () with
  | LNil -> nil
  | input ->
      let f1 = choose_op () in
      let f2 = choose_op () in
      let (z1,z2) = split (fun () -> input) in
      lappend (f1 z1) (f2 z2)
;;

(* Testing on a simpler example *)
let main_simple () =
  let input = to_lcons [A; B; C] in
  lobserve (transform input)
    [Asharp; C]
;;

(*
Inference.timeit 
  (fun () -> sample_importance (random_selector 17) 2000 main_simple);;
Time spent: 2.50602 sec
- : unit pV = [(0.00134795555555555671, V ())]

Inference.timeit 
  (fun () -> sample_importance (random_selector 17) 10000 main_simple);;
Time spent: 11.9895 sec
- : unit pV = [(0.00194459657407407456, V ())]

Inference.timeit 
  (fun () -> sample_importance (random_selector 17) 20000 main_simple);;
Time spent: 24.0791 sec
- : unit pV = [(0.00179150412037037054, V ())]

Inference.timeit 
  (fun () -> sample_importance (random_selector 17) 30000 main_simple);;
Time spent: 36.0914 sec
- : unit pV = [(0.00189214598765431318, V ())]

I think we observe the convergence already...

Old testing:
let mstree = reify0 main_simple;;
timeit (fun () -> sample_dist 17 2000 (fun x -> x) mstree);;
Time spent: 3.01 sec
sample_importance 17 2000 main_simple;;
- : unit pV = [(0.0023140625, V ())]

sample_importance 17 10000 main_simple;;
- : unit pV = [(0.0021337187499999989, V ())]

sample_importance 17 45000 main_simple;;
- : unit pV = [(0.00189809789737654402, V ())]

sample_importance 17 90000 main_simple;;
- : unit pV = [(0.00199413324652778379, V ())]

Trying a few optimizations:
timeit (fun () -> sample_dist 17 2000 (fun x -> x) (shallow_explore 1 mstree));;
sample_importance: done 2000 worlds
Time spent: 2.71875 sec
- : unit pV = [(0.00188981770833333406, V ())]

timeit (fun () -> sample_dist 17 2000 (fun x -> x) (shallow_explore 2 mstree));;
sample_importance: done 2000 worlds
Time spent: 2.46094 sec
- : unit pV = [(0.00181322916666666785, V ())]

timeit (fun () -> sample_dist 17 2000 (fun x -> x) (shallow_explore 3 mstree));;
sample_importance: done 2000 worlds
Time spent: 2.28906 sec
- : unit pV = [(0.0020492708333333348, V ())]

timeit (fun () -> sample_dist 17 10000 (fun x -> x) (shallow_explore 3 mstree));;
sample_importance: done 10000 worlds
Time spent: 11.3047 sec
- : unit pV = [(0.00214332291666666621, V ())]

*)

(* IBAL gives
System8/sample MUSIC.NEW/music-simple.ibl 10
Number of samples = 44883
Probability of evidence = 0.00194884

System8/sample MUSIC.NEW/music-simple.ibl 30
Number of samples = 136378
Probability of evidence = 0.00193426
*)

let music2_main src dst =
  let input = to_lcons src in
  lobserve (transform input) dst
;;

(* The main function: corresponds to music.src1.dst1.ibl *)
let main () = 
  music2_main [E; A; C; E; A; C; B; A; Gsharp; A]
              [E; D; C; B; A; B]
;;

let [(p, V ())] = sample_importance (random_selector 17) 70000 main
in Printf.printf "Probability of evidence: %g" p;;
exit 0;;

(* Without any letlazy:
sample_importance: done 10000 worlds
Probability of evidence: 3.63636e-07

It took about 2 minutes on my Asus!

On the following platform:
   Intel(R) Pentium(R) 4 CPU 2.00GHz (1993.95-MHz 686-class CPU)
   1GB main memory
   FreeBSD 6.2-STABLE

Performing 70,000 samples produces
Probability of evidence: 9.5491e-07
111.41 real        98.58 user         0.95 sys
[machine was busy, so real time reflects other activities that happened
at that time]

      1492  maximum resident set size
       115  average shared memory size
       562  average unshared data size
       127  average unshared stack size
       204  page reclaims
         0  page faults
         0  swaps
         0  block input operations
         0  block output operations
         0  messages sent
         0  messages received
         0  signals received
         1  voluntary context switches
    101630  involuntary context switches

*)

(* With letlazy, thread_local, first version:
sample_importance: done 70000 worlds
Probability of evidence: 1.66696e-06
250.78 real       243.22 user         2.31 sys
      1448  maximum resident set size
       116  average shared memory size
       568  average unshared data size
       128  average unshared stack size
       207  page reclaims
         0  page faults
         0  swaps
         0  block input operations
         0  block output operations
         0  messages sent
         0  messages received
         0  signals received
         1  voluntary context switches
    250459  involuntary context switches

Compilation finished at Tue Mar 10 23:54:59

Second version: a minute faster.
Probability of evidence: 1.66696e-06
197.10 real       190.81 user         1.91 sys
      1448  maximum resident set size
       116  average shared memory size
       568  average unshared data size
       128  average unshared stack size
       207  page reclaims
         0  page faults
         0  swaps
         0  block input operations
         0  block output operations
         0  messages sent
         0  messages received
         0  signals received
         1  voluntary context switches
    196347  involuntary context switches

*)
(* with the shallow_explore at depth 3:
sample_importance: done 70000 worlds
Probability of evidence: 1.2801e-06      
211.19 real       205.19 user         2.08 sys
      5368  maximum resident set size
       116  average shared memory size
      4533  average unshared data size
       128  average unshared stack size
      1185  page reclaims
         0  page faults
         0  swaps
         0  block input operations
         0  block output operations
         0  messages sent
         0  messages received
         0  signals received
         1  voluntary context switches
    210833  involuntary context switches
*)

(* With pre-computed transposition mappings:
 Results are the same, but computed faster.

sample_reify: done 70000 worlds
Probability of evidence: 1.2801e-06
157.56 real       156.70 user         0.04 sys
      3604  maximum resident set size
       115  average shared memory size
       619  average unshared data size
       127  average unshared stack size
       705  page reclaims
         0  page faults
         0  swaps
         0  block input operations
         0  block output operations
         0  messages sent
         0  messages received
         0  signals received
         1  voluntary context switches
     19032  involuntary context switches

Compilation finished at Tue Apr 21 02:37:42

After making reify0 and dist more general to permit nesting. The overhead
of nesting seems negligible, comprared with the above results.
sample_importance: done 70000 worlds
Probability of evidence: 1.2801e-06
158.63 real       157.38 user         0.02 sys
      3584  maximum resident set size
       115  average shared memory size
       619  average unshared data size
       127  average unshared stack size
       706  page reclaims
         0  page faults
         0  swaps
         0  block input operations
         0  block output operations
         0  messages sent
         0  messages received
         0  signals received
         1  voluntary context switches
     19345  involuntary context switches

Compilation finished at Wed Apr 29 18:41:50

New version of delimcc, Oct 2009
sample_importance: done 70000 worlds
Probability of evidence: 1.2801e-06
144.07 real       142.67 user         0.03 sys
      3472  maximum resident set size
       115  average shared memory size
       619  average unshared data size
       127  average unshared stack size
       708  page reclaims
         0  page faults
         0  swaps
         0  block input operations
         0  block output operations
         0  messages sent
         0  messages received
         0  signals received
         1  voluntary context switches
     17868  involuntary context switches

Compilation finished at Tue Oct 13 18:27:42

Using shift0 instead of shift:
sample_importance: done 70000 worlds
Probability of evidence: 1.2801e-06
141.16 real       136.12 user         0.00 sys
      3472  maximum resident set size
       115  average shared memory size
       619  average unshared data size
       127  average unshared stack size
       708  page reclaims
         0  page faults
         0  swaps
         0  block input operations
         0  block output operations
         0  messages sent
         0  messages received
         0  signals received
         1  voluntary context switches
     17080  involuntary context switches

Compilation finished at Tue Oct 13 20:39:19

Version Aug 2010, for the native-code compatible version:
sample_importance: done 70000 worlds
Probability of evidence: 1.2801e-06
149.93 real       148.28 user         0.03 sys
      3676  maximum resident set size
       119  average shared memory size
       615  average unshared data size
       127  average unshared stack size
       730  page reclaims
         0  page faults
         0  swaps
         0  block input operations
         0  block output operations
         0  messages sent
         0  messages received
         0  signals received
         1  voluntary context switches
     18446  involuntary context switches

Compilation finished at Wed Aug 11 18:02:41

native code:
sample_importance: done 70000 worlds
Probability of evidence: 1.2801e-06
151.79 real       150.49 user         0.05 sys
      3096  maximum resident set size
       179  average shared memory size
       554  average unshared data size
       127  average unshared stack size
       641  page reclaims
         0  page faults
         0  swaps
         0  block input operations
         0  block output operations
         0  messages sent
         0  messages received
         0  signals received
         2  voluntary context switches
     18945  involuntary context switches

Compilation finished at Wed Aug 11 18:06:15

Version Aug 21, 2010:
byte-code:
Probability of evidence: 1.2801e-06
151.82 real       150.40 user         0.04 sys
      3668  maximum resident set size
       119  average shared memory size
       615  average unshared data size
       127  average unshared stack size
       730  page reclaims
         0  page faults
         0  swaps
         0  block input operations
         0  block output operations
         0  messages sent
         0  messages received
         0  signals received
         1  voluntary context switches
     19452  involuntary context switches

native code:
sample_importance: done 70000 worlds
Probability of evidence: 1.2801e-06
151.78 real       149.66 user         0.05 sys
      3068  maximum resident set size
       179  average shared memory size
       554  average unshared data size
       127  average unshared stack size
       641  page reclaims
         0  page faults
         0  swaps
         0  block input operations
         0  block output operations
         0  messages sent
         0  messages received
         0  signals received
         2  voluntary context switches
     19736  involuntary context switches

*)

