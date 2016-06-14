(* Correlated memoization: building stochastic injective functions,
   or sampling permutations lazily.

   We use Shared variables as logic variables, and
   memoized functions [0..N-1] -> [0..N-1] as
   sequences of logic variables upon the `all different' constraint.
   Such sequences appears prominently in many logic puzzles, such
   as the Zebra puzzle.

   This file in particular relies on letlazy and memo functions of Hansei,
   to define shared probabilistic computations and memoized 
   stochastic functions.
*)

open ProbM;;

(*
   HANSEI supports lets us build stochastic _functions_. Compare the
   probability tables of (f1 0, f1 1, f1 0, f1 1) vs
   (f2 0, f2 1, f2 0, f2 1) below.
*)

  (* Uniformly select an element from a list *)
let uniformly_list lst = List.nth lst (uniform (List.length lst));;
  (* val uniformly_list : 'a list -> 'a = <fun> *)

let [(0.0625, Ptypes.V (1, 1, 1, 1)); (0.0625, Ptypes.V (1, 1, 1, 0));
     (0.0625, Ptypes.V (1, 1, 0, 1)); (0.0625, Ptypes.V (1, 1, 0, 0));
     (0.0625, Ptypes.V (1, 0, 1, 1)); (0.0625, Ptypes.V (1, 0, 1, 0));
     (0.0625, Ptypes.V (1, 0, 0, 1)); (0.0625, Ptypes.V (1, 0, 0, 0));
     (0.0625, Ptypes.V (0, 1, 1, 1)); (0.0625, Ptypes.V (0, 1, 1, 0));
     (0.0625, Ptypes.V (0, 1, 0, 1)); (0.0625, Ptypes.V (0, 1, 0, 0));
     (0.0625, Ptypes.V (0, 0, 1, 1)); (0.0625, Ptypes.V (0, 0, 1, 0));
     (0.0625, Ptypes.V (0, 0, 0, 1)); (0.0625, Ptypes.V (0, 0, 0, 0))]
=
exact_reify (fun () -> 
  let f1 = function
    | 0 -> uniformly_list [0;1]
    | 1 -> uniformly_list [0;1]
  in 
  (f1 0, f1 1, f1 0, f1 1));;


let [(0.25, Ptypes.V (1, 1, 1, 1)); (0.25, Ptypes.V (1, 0, 1, 0));
     (0.25, Ptypes.V (0, 1, 0, 1)); (0.25, Ptypes.V (0, 0, 0, 0))]
=
exact_reify (fun () ->
  let f2 = memo (function
    | 0 -> uniformly_list [0;1]
    | 1 -> uniformly_list [0;1])
  in 
  (f2 0, f2 1, f2 0, f2 1));;

(* The memoized function f2 yields the same values when applied
   to the same arguments. The values may differ in different worlds.

   We also see that (f2 0) and (f2 1) are independently distributed
   random values. Sometimes we want to introduce dependence.
   In particular, we may wish for the result of (f 0) be always different
   from the result of (f 1). In general, given a list L of N elements, 
   we would like to define a stochastic injective function 
   f :: [0..N-1] -> L. When applied to different arguments the function 
   must yield different results. Now, the random variables (f x) 
   for different x are correlated.
*)

(* The simplest way to implement a stochastic injective function
   is by rejection sampling:
   we use f2 as it was but reject the worlds in which f2 is not injective.
*)

let [(0.25, Ptypes.V (1, 0, 1, 0)); (0.25, Ptypes.V (0, 1, 0, 1))]
=
exact_reify (fun () ->
  let f2 = memo (function
    | 0 -> uniformly_list [0;1]
    | 1 -> uniformly_list [0;1])
  in
  let f3 x = 
    if f2 0 == f2 1 then fail ();
    f2 x
  in
  (f3 0, f3 1, f3 0, f3 1));;

(* We obtain the desired result: (f3 x) is a function (applying it to
   the same arguments yields the same results), and f3 is injective.

   The function f3 is clearly inefficient: the fact that the weights
   in the resulting probability table sum to 0.5 rather than 1.0
   reveal that we have wasted half of the choice space.

   It is much better to sample from the `right' worlds upfront and avoid
   generating the worlds that we have to reject later.
*)


(* To avoid rejections, we observe that our goal is to sample from all 
   permutations of the given list. That gives us f4:
*)

let [(0.5, Ptypes.V (1, 0, 1, 0)); (0.5, Ptypes.V (0, 1, 0, 1))]
 =
exact_reify (fun () ->
  let perms = letlazy (fun () -> uniformly_list [ [0;1]; [1;0] ]) in
  let f4 = List.nth (perms ())
  in 
  (f4 0, f4 1, f4 0, f4 1));;

(* The function f4 is too an injective function; now we don't waste
   any choice space.

   Yet f4 isn't as efficient as we would like it to be. We have to
   generate all permutations of the input list first, and then sample
   from it. Given the list of length N, the first application of
   |f4| to any argument involves sampling from N! choices.
   Further applications of f4 involve no choices.
   What if the value of (f4 x) turns out inconsistent with further
   observations? We will have to reject (N-1)! already made choices.
   Again, we have wasted a lot of choice space.

   We can reduce the overall waste by computing permutations
   lazily. Determining (f5 0) requires only N choices,
   (f5 1) -- N*(N-1) choices, etc.
*)


(* Compute a lazy permutation of a given list.
   We return a list of _correlated_ random variables.
   Sampling from a variable i returns a value that is different
   from the samples of the variables 0..i-1.
*)


(* Split a list at the given element n and return the zipper:
   first (n-1) elements, in the inverse order, and the tail of the list.
   The n-th element is at the head of the tail.
   If the given list has fewer than n elements, the tail will be empty.
*)
let split_at : int -> 'a list -> 'a list * 'a list =
   fun n lst ->
   let rec loop acc = function
   | (0,lst)  -> (acc, lst)
   | (n,[])   -> (acc,[])
   | (n,h::t) -> loop (h::acc) (pred n, t)
   in loop [] (n,lst)
;;

(*
let ([], [1; 2; 3]) = split_at 0 [1;2;3];;
let ([1], [2; 3])   = split_at 1 [1;2;3];;
let ([2; 1], [3])   = split_at 2 [1;2;3];;
let ([3; 2; 1], []) = split_at 3 [1;2;3];;
*)

(* Useful auxiliary function:
   uniformly select one element from a list and return it and the remainder
*)
let uniformly_uncons = function
   | []  -> fail ()
   | [x] -> (x,[])
   | xs  -> 
   let n = List.length xs in
   let i = uniform n in
   let (prev,h::next) = split_at i xs in
   (h, List.rev_append prev next)
;;

(*
let [(0.333333333333333315, Ptypes.V (3, [1; 2]));
     (0.333333333333333315, Ptypes.V (2, [1; 3]));
     (0.33333333333333337, Ptypes.V (1, [2; 3]))] =
   exact_reify (fun () -> uniformly_uncons [1;2;3]);;
*)

let lazy_permutation : 'a list -> (unit -> 'a) list =
   let rec loop prev_var = function
   | [_]   -> [fun () -> match prev_var () with (_,[x]) -> x]
   | _::t  -> 
   let new_var = letlazy (fun () -> uniformly_uncons (snd (prev_var ()))) in
   (fun () -> fst (new_var ())) :: loop new_var t
   in 
   function
   | []   -> []
   | [x]  -> [fun () -> x]
   | (_::t) as lst  -> 
   let var0 = letlazy (fun () -> uniformly_uncons lst) in
   (fun () -> fst (var0 ())) :: loop var0 t
;;

let (0.999999999999999667,
 [(0.0416666666666666782, Ptypes.V [4; 3; 2; 1]);
  (0.0416666666666666782, Ptypes.V [4; 3; 1; 2]);
  (0.0416666666666666782, Ptypes.V [4; 2; 3; 1]);
  (0.0416666666666666782, Ptypes.V [4; 2; 1; 3]);
  (0.0416666666666666852, Ptypes.V [4; 1; 3; 2]);
  (0.0416666666666666852, Ptypes.V [4; 1; 2; 3]);
  (0.0416666666666666782, Ptypes.V [3; 4; 2; 1]);
  (0.0416666666666666782, Ptypes.V [3; 4; 1; 2]);
  (0.0416666666666666782, Ptypes.V [3; 2; 4; 1]);
  (0.0416666666666666782, Ptypes.V [3; 2; 1; 4]);
  (0.0416666666666666852, Ptypes.V [3; 1; 4; 2]);
  (0.0416666666666666852, Ptypes.V [3; 1; 2; 4]);
  (0.0416666666666666782, Ptypes.V [2; 4; 3; 1]);
  (0.0416666666666666782, Ptypes.V [2; 4; 1; 3]);
  (0.0416666666666666782, Ptypes.V [2; 3; 4; 1]);
  (0.0416666666666666782, Ptypes.V [2; 3; 1; 4]);
  (0.0416666666666666852, Ptypes.V [2; 1; 4; 3]);
  (0.0416666666666666852, Ptypes.V [2; 1; 3; 4]);
  (0.0416666666666666782, Ptypes.V [1; 4; 3; 2]);
  (0.0416666666666666782, Ptypes.V [1; 4; 2; 3]);
  (0.0416666666666666782, Ptypes.V [1; 3; 4; 2]);
  (0.0416666666666666782, Ptypes.V [1; 3; 2; 4]);
  (0.0416666666666666852, Ptypes.V [1; 2; 4; 3]);
  (0.0416666666666666852, Ptypes.V [1; 2; 3; 4])])
=
Inference.normalize (exact_reify (
  fun () -> List.map (fun th -> th ()) (lazy_permutation [1;2;3;4])));;

let [(0.166666666666666657, Ptypes.V (3, 2, 3, 2));
     (0.166666666666666657, Ptypes.V (3, 1, 3, 1));
     (0.166666666666666657, Ptypes.V (2, 3, 2, 3));
     (0.166666666666666657, Ptypes.V (2, 1, 2, 1));
     (0.166666666666666685, Ptypes.V (1, 3, 1, 3));
     (0.166666666666666685, Ptypes.V (1, 2, 1, 2))] =
exact_reify (fun () ->
  let perms = lazy_permutation [1;2;3] in
  let f5 n = List.nth perms n ()
  in 
  (f5 0, f5 1, f5 0, f5 1));;



(*
 Given a sorted list of distinct integers lst and an integer j, insert j
 into the appropriate place in lst and return j and the new lst.

 The integer j is not given directly, however. Instead of j, the
 function receives an integer i, which is j minus the number of
 elements in lst that are smaller than j.
*)

let insert_shift i lst =
  let rec loop acc i = function
  | []     -> (i,List.rev (i::acc))
  | (h::_) as lst when h > i -> (i,List.rev_append acc (i::lst))
  | (h::t) -> loop (h::acc) (succ i) t
  in
  loop [] i lst
;;

(*
let (0, [0]) = insert_shift 0 [];;

let (1, [0; 1]) = insert_shift 0 [0];;

let (0, [0; 1]) = insert_shift 0 [1];;

let (2, [1; 2]) = insert_shift 1 [1];;
let (3, [1; 3]) = insert_shift 2 [1];;

let (2, [0; 1; 2]) = insert_shift 0 [0;1];;
let (0, [0; 1; 2]) = insert_shift 0 [1;2];;
let (3, [1; 2; 3]) = insert_shift 1 [1;2];;
*)

(* Compute the sequence of N all-different random variables
   with the range [0..N-1].
   A sample from a sequence has no duplicates, and is
   a permutation from [0..N-1]
*)

let lazy_permutation_ins : int -> (unit -> int) list =
   let rec loop prev_var = function
   | 1 -> [fun () -> match prev_var () with (_,lst) -> 
                        fst (insert_shift 0 lst)]
   | n -> 
   let new_var = letlazy (fun () -> 
     let i = uniform n in insert_shift i (snd (prev_var ()))) in
   (fun () -> fst (new_var ())) :: loop new_var (n-1)
   in 
   function
   | 0  -> []
   | 1  -> [fun () -> 0]
   | n when n > 1 ->
   let var0 = letlazy (fun () -> let i = uniform n in (i,[i])) in
   (fun () -> fst (var0 ())) :: loop var0 (n-1)
;;


let (0.999999999999999667,
 [(0.0416666666666666782, Ptypes.V [3; 2; 1; 0]);
  (0.0416666666666666782, Ptypes.V [3; 2; 0; 1]);
  (0.0416666666666666782, Ptypes.V [3; 1; 2; 0]);
  (0.0416666666666666782, Ptypes.V [3; 1; 0; 2]);
  (0.0416666666666666852, Ptypes.V [3; 0; 2; 1]);
  (0.0416666666666666852, Ptypes.V [3; 0; 1; 2]);
  (0.0416666666666666782, Ptypes.V [2; 3; 1; 0]);
  (0.0416666666666666782, Ptypes.V [2; 3; 0; 1]);
  (0.0416666666666666782, Ptypes.V [2; 1; 3; 0]);
  (0.0416666666666666782, Ptypes.V [2; 1; 0; 3]);
  (0.0416666666666666852, Ptypes.V [2; 0; 3; 1]);
  (0.0416666666666666852, Ptypes.V [2; 0; 1; 3]);
  (0.0416666666666666782, Ptypes.V [1; 3; 2; 0]);
  (0.0416666666666666782, Ptypes.V [1; 3; 0; 2]);
  (0.0416666666666666782, Ptypes.V [1; 2; 3; 0]);
  (0.0416666666666666782, Ptypes.V [1; 2; 0; 3]);
  (0.0416666666666666852, Ptypes.V [1; 0; 3; 2]);
  (0.0416666666666666852, Ptypes.V [1; 0; 2; 3]);
  (0.0416666666666666782, Ptypes.V [0; 3; 2; 1]);
  (0.0416666666666666782, Ptypes.V [0; 3; 1; 2]);
  (0.0416666666666666782, Ptypes.V [0; 2; 3; 1]);
  (0.0416666666666666782, Ptypes.V [0; 2; 1; 3]);
  (0.0416666666666666852, Ptypes.V [0; 1; 3; 2]);
  (0.0416666666666666852, Ptypes.V [0; 1; 2; 3])])
=
Inference.normalize (exact_reify (
  fun () -> List.map (fun th -> th ()) (lazy_permutation_ins 4)));;

let [(0.166666666666666657, Ptypes.V (2, 1, 2, 1));
     (0.166666666666666657, Ptypes.V (2, 0, 2, 0));
     (0.166666666666666657, Ptypes.V (1, 2, 1, 2));
     (0.166666666666666657, Ptypes.V (1, 0, 1, 0));
     (0.166666666666666685, Ptypes.V (0, 2, 0, 2));
     (0.166666666666666685, Ptypes.V (0, 1, 0, 1))]
=
exact_reify (fun () ->
  let perms = lazy_permutation_ins 3 in
  let f5 n = List.nth perms n ()
  in 
  (f5 0, f5 1, f5 0, f5 1));;

