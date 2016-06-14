(* Nested sampling and inference
   Distributions parameterized over a distribution
*)

open Ptypes
open ProbM;;

(* ------------------------------ Trivial example of nested distributions *)

(* The problem: suppose I'm given a coin: it can be either a
   fair coin, or a coin that always flips to true.
   I use a sampling procedure to determine the distribution of the coin.
   What is the distribution of the distribution?
*)

let testn11 () =
  let coin = dist [(0.5, (fun () -> flip 0.5)); (0.5, (fun () -> true))] in
  exact_reify coin;;

let testn12 () =
  let coin = dist [(0.5, (fun () -> flip 0.5)); (0.5, (fun () -> true))] in
  sample_rejection (random_selector 17) 10 coin;;

let [(0.5, V [(1., V true)]); (0.5, V [(0.5, V true); (0.5, V false)])] =
  exact_reify testn11;;
 
let [(0.5, V [(1., V true)]); (0.5, V [(0.6, V true); (0.4, V false)])] =
  exact_reify testn12;;

let [(0.5, V [(1., V true)]); (0.5, V [(0.6, V true); (0.4, V false)])] =
  sample_rejection (random_selector 17) 10 testn12;;


(* A different representation of the same example *)
let testn21 () =
    let coin_choice = flip 0.5 in
    exact_reify (fun () -> flip 0.5 || coin_choice)
;;

let [(0.5, V [(1., V true)]); (0.5, V [(0.5, V true); (0.5, V false)])] =
  exact_reify testn21;;

let testn22 () =
    let coin_choice = flip 0.5 in
    sample_rejection (random_selector 17) 10 (fun () -> flip 0.5 || coin_choice)
;;

let [(0.5, V [(1., V true)]); (0.5, V [(0.6, V true); (0.4, V false)])] =
  exact_reify testn22;;

let testn21' () =
    let coin_choice = flip 0.5 in
    exact_reify (fun () -> coin_choice || flip 0.5)
;;

let [(0.5, V [(1., V true)]); (0.5, V [(0.5, V true); (0.5, V false)])] =
  exact_reify testn21';;

(* As expected, the results are the same *)

(* ------------------------------ Nested inference and lazy variables *)

(* Now we use a lazy variable in the outer scope *)

let testnl10 () =
    let coin_choice = letlazy (fun () ->
      let v = flip 0.5 in
      Printf.printf "Evaluating coin choice: %b\n" v; v) in
    exact_reify (fun () -> coin_choice () || flip 0.5)
;;

let [(1., V [(0.75, V true); (0.25, V false)])] =
  exact_reify testnl10;;

(* But the results are now wrong! This is because laziness reorders effects.
   With nesting, it matters: effects inside and outside don't commute.
   The above example is equivalent to
    let testnl11_ () =
      exact_reify (fun () -> flip 0.5 || flip 0.5);;
   which has quite a different meaning.
*)

(* Here is our solution *)
(* We should use a more general primitive, which is nesting-safe:
   letlazy_nesting.
   This primitive can be used without nesting, at some degradation in
   performance.
*)

let testnl11 () =
    let coin_choice = letlazy_nesting (fun () ->
      let v = flip 0.5 in
      Printf.printf "Evaluating coin choice: %b\n" v; v) in
    exact_reify (fun () -> coin_choice () || flip 0.5)
;;

let [(0.5, V [(1., V true)]); (0.5, V [(0.5, V true); (0.5, V false)])] =
  exact_reify testnl11;;

(* Now we get the expected result *)

(* More tests *)

let testnl12 () =
    let coin_choice = letlazy_nesting (fun () ->
      let v = flip 0.5 in
      Printf.printf "Evaluating coin choice: %b\n" v; v) in
    exact_reify (fun () -> flip 0.5 || coin_choice ())
;;

let [(0.5, V [(1., V true)]); (0.5, V [(0.5, V true); (0.5, V false)])] =
  exact_reify testnl12;;

(* More complex test *)
let testnl13 () =
    let coin_choice = letlazy_nesting (fun () ->
      let v = flip 0.5 in
      Printf.printf "Evaluating coin choice: %b\n" v; v) in
    let v1 = exact_reify (fun () -> let v = flip 0.5 in 
                            (v, coin_choice (), coin_choice ())) in
    (coin_choice (), coin_choice (), v1)
;;

let [(0.5,
  V (true, true, [(0.5, V (true, true, true)); (0.5, V (false, true, true))]));
 (0.5,
  V
   (false, false,
    [(0.5, V (true, false, false)); (0.5, V (false, false, false))]))] =
  exact_reify testnl13;;

let
[(0.6,
  V (true, true, [(0.5, V (true, true, true)); (0.5, V (false, true, true))]));
 (0.4, V (false, false, [(0.5, V (true, false, false)); (0.5, V (false, false, false))]))]
=
  sample_rejection (random_selector 17) 10 testnl13;;


(* ------------------------------ Nested approximate inference: rejection *)

let tflip2_noshared () =   (* independent flips *)
  flip 0.5 && flip 0.5;;

let tf2_nested n selector =
  sample_rejection selector n tflip2_noshared;;

let () = assert (
  tf2_nested 100 (random_selector 1)
    = [(0.24, V true); (0.76, V false)]);;

let [(0.25, V [(1., V true)]); (0.75, V [(1., V false)])] =
  exact_reify (fun () -> tf2_nested 1 dist_selector);;
(* 3 worlds *)

let [(0.0625, V [(1., V true)]); (0.5625, V [(1., V false)]);
     (0.375, V [(0.5, V true); (0.5, V false)])] =
  exact_reify (fun () -> tf2_nested 2 dist_selector);;
(* 9 samples, 2 worlds each
   It is patent we compute the distribution over distributions *)

let [(0.24, V [(1., V true)]); (0.76, V [(1., V false)])] =
sample_rejection (random_selector 1) 100 
    (fun () -> tf2_nested 1 dist_selector);;

(* we see that nested rejection sampling with 1 sample is
   the identity transformation of the model. It adds the layer
   of interpretive overhead.
*)

let x = sample_rejection (random_selector 1) 100 
    (fun () -> tf2_nested 3 dist_selector);;
let
[(0.42, V [(1., V false)]);
 (0.18, V [(0.66666666666666663, V true); (0.333333333333333315, V false)]);
 (0.4, V [(0.333333333333333315, V true); (0.66666666666666663, V false)])] =
sample_rejection (random_selector 1) 100 
    (fun () -> tf2_nested 3 dist_selector);;
(* If we flatten the table, we get the results of the non-nested
 sample_importance with 100 samples and the seed of 1
*)

let testnl14 () =
    let coin_choice = letlazy_nesting (fun () ->
      let v = flip 0.5 in
      Printf.printf "Evaluating coin choice: %b\n" v; v) in
    let v1 = sample_rejection dist_selector 10 
	(fun () -> let v = flip 0.5 in 
                   (v, coin_choice (), coin_choice ())) in
    (coin_choice (), coin_choice (), v1)
;;

(*
let [(0.5,
  V (true, true, [(0.7, V (true, true, true)); (0.3, V (false, true, true))]));
 (0.5,
  V
   (false, false,
    [(0.7, V (true, false, false)); (0.3, V (false, false, false))]))] =
  exact_reify testnl14;;
*)

let x =   sample_rejection (random_selector 17) 10 testnl14;;
let [(0.1, V (true, true, [(0.7, V (true, true, true)); (0.3, V (false, true, true))]));
     (0.2, V (true, true, [(0.5, V (true, true, true)); (0.5, V (false, true, true))]));
     (0.1, V (false, false, [(0.7, V (true, false, false)); (0.3, V (false, false, false))]));
     (0.1, V (false, false, [(0.5, V (true, false, false)); (0.5, V (false, false, false))]));
     (0.1, V (false, false, [(0.4, V (true, false, false)); (0.6, V (false, false, false))]));
     (0.3, V (false, false, [(0.3, V (true, false, false)); (0.7, V (false, false, false))]));
     (0.1, V (false, false, [(0.2, V (true, false, false)); (0.8, V (false, false, false))]))] =
  sample_rejection (random_selector 17) 10 testnl14;;


(* ------------------------------ Nested importance sampling *)

let drunk_coin () = 			(* The drunken coin from samplingM.ml *)
  let x = flip 0.5 in
  let lost = flip 0.9 in
  if lost then fail () else x;;

(* Compute AND of n tosses of the drunk coin *)
let rec dcoin_and = function
  | 1 -> drunk_coin ()
  | n -> drunk_coin () && dcoin_and (n-1)
;;

(* exact result:
  = [(9.76562499999997764e-14, V true); (0.0526315789473632695, V false)]);;
*)

(* The baseline: top-level importance sampling *)
let [(0.052301965599999993, V false)] =
sample_importance (random_selector 17) 100 (fun () -> dcoin_and 10);;

let [(0.052301965599999993, V [(1., V false)]); (0.9476980344, V [])] =
 sample_importance (random_selector 17) 100
  (fun () -> sample_rejection dist_selector 1 (fun () -> dcoin_and 10));;
(* Demonstrating once again that nested_rejection_sampling of one
   sample is the identity transformation. Note that the nested
   inference can fail -- very often in our case.
   In the probability table returned by the outer inference, the probabilities
   sum to one now.
*)
let
  [(0.5, V [(0.0549999999999999864, V false)]);
   (0.25, V [(0.0504999999999999893, V false)]);
   (0.125, V [(0.0500499999999999903, V false)]);
   (0.0625, V [(0.050004999999999987, V false)]);
   (0.03125, V [(0.0500004999999999894, V false)]);
   (0.015625, V [(0.0500000499999999903, V false)]);
   (0.0078125, V [(0.0500000049999999863, V false)]);
   (0.00390625, V [(0.0500000004999999886, V false)]);
   (0.001953125, V [(0.0500000000499999861, V false)]);
   (0.001953125,
    V [(4.99999999999998855e-11, V true); (0.0499999999999999889, V false)])] =
sample_importance (random_selector 17) 100
  (fun () -> sample_importance dist_selector 1 (fun () -> dcoin_and 10));;
(* The probabilities in the outer probability table sum to one.
   there is a chance the unlikely solution V true is found.
*)

let dcoin_and_true n = dcoin_and n || fail ();;

let [(0.999999999999999889, V [])] =
sample_importance (random_selector 1) 100
  (fun () -> sample_rejection dist_selector 1 (fun () -> dcoin_and_true 10));;
(* Again showing that nested rejection of 1 sample is the identity
   transform. The computed prob is exactly the same as that for
   sample_reify 1 100 for the original model.
*)

let [(0.001953125, V [(4.99999999999998855e-11, V true)]);
     (0.998046875, V [])] =
sample_importance (random_selector 1) 100
  (fun () -> sample_importance dist_selector 1 (fun () -> dcoin_and_true 10));;
(*
4.99999999999998855e-11 *. 0.001953125 is 9.76562499999997764e-14,
which is the exact result.
*)

let
[(1.953125e-05, V [(2.99999999999999328e-12, V true)]);
 (0.01017578125, V [(1.99999999999999552e-12, V true)]);
 (0.10154296875, V [(9.99999999999997758e-13, V true)]);
 (0.88826171875, V [])] =
sample_importance (random_selector 1) 100
  (fun () -> sample_importance dist_selector 50 (fun () -> dcoin_and_true 10));;


(* Extended example from the paper *)

let prob_of (v_test : 'a) (pv : 'a pV) =
  try fst (List.find (fun (p, V v) -> v = v_test) pv) with Not_found -> 0.;;

(* 
  Choose a coin that is either fair or completely biased
  for |true|, with equal probability.  Let $p$ be the probability that 
  flipping the coin yields |true|.  What is the probability that $p$ is at
  least 0.3?  It is $1$, of course, because both 0.5 and 1 are at least 0.3.
  In the code below, the |at_least 0.3 true| tests if a given 
  probability table assigns probability at least 0.3 to the outcome |true|.
*)

let at_least prob v pv = prob_of v pv >= prob;;


let test_nest p inferencer () =
    let x = flip 0.5 in
    at_least p true (inferencer (fun () -> flip 0.5 || x))
;;

let test_nest_lazy p inferencer () =
    let x = letlazy_nesting (fun () -> flip 0.5) in
    at_least p true (inferencer (fun () -> flip 0.5 || x ()))
;;

let thresholds =
    let rec loop n l = if n > 15 then l
                       else loop (succ n) (float_of_int n /. 10. :: l)
    in loop (-5) [];;

let () = assert (
    List.for_all
      (fun p -> let expected_exact =
                    if p <= 0.5 then 1.0 else
                    if p <= 1.0 then 0.5 else
                    0.0 in
                let expected_sample =
                    if p <= 0.0 then 1.0 else
                    if p <= 0.5 then 0.875 else
                    if p <= 1.0 then 0.625 else
                    0.0 in
                expected_exact  = 
		prob_of true (exact_reify (test_nest p exact_reify)) &&
                expected_exact  = 
		prob_of true (exact_reify (test_nest_lazy p exact_reify)) &&
		expected_sample = 
		prob_of true (exact_reify (test_nest p
					 (sample_rejection dist_selector 2))) &&
		expected_sample = 
		prob_of true (exact_reify (test_nest_lazy p
					 (sample_rejection dist_selector 2)))
      )
      thresholds
);;

(* Consider the following game (we give realistic instances below)

We can make one of the moves M1...Mn with the corresponding probabilities
p_M1 ... p_Mn (for example, in a board game, we cast a die and make the move
with as many steps as indicated). If we make the move Mi, the opponent can 
make its moves (etc?) and so bring the game to some position Sj.
Some of these positions we consider unsatisfactory. We are interested in the
(estimate of) the probability of the unsatisfactory position. If this
probability is greater than some threshold (risk), we consider that a failure.
We are interested in the distribution of non-failing moves.

One may consider the above scenario a generalization of the alpha-beta
algorithm, where we use sampling to determine the approximate
distribution of positions and we are willing to take a risk of a bad
position.  That is, the fact that a move can lead to a bad, for us,
outcome does not disqualify the move -- provided that the possibility
of the bad outcome is sufficiently small.

Some concrete instances of the scenario: drug trials. It seems that many
planning-as-inference problems involve the component `proceed with risk'.
Estimating the risk necessarily requires nested sampling. The estimation 
of risk must be efficient; for example, if our risk threshold is 10^-4,
we would need to do a lot of sampling to be certain the risk of a given
move stays below the threshold.

Given below is a sample of planning-as-inference with risk, a modification
of red-light game.

*)

(*
 Inference-as-planning with risk.
 The following is a variation of the red-light game of the Church paper,
 which was in turn inspired by [21].
  
We need to cross N intersections; each crossing takes one time-step.
When we approach the intersection, the light may be either green or
red.  If the light is red, we can wait for a time-step. With the
probability of cheating, we may proceed even if the light is red. When
we go on red light, we may get caught. The probability of getting
caught depends on the intersection (different intersections have different
chances of being closely monitored by police), on the time of day, 
and just on bad lack. We model the dependency on the time of day
by the dependency on the number of time steps already taken.
We want to determine the optimal probability of cheating.

*)

(* parameters of the model *)
let n = 5
 (* Probability the intersection #i is monitored by police *)
let police_monitoring = Array.of_list [0.1; 0.2; 0.1; 0.2; 0.2]
let bad_luck = 0.1
let maxrisk = 0.2
;;


let noisy_or a astrength b bstrength baserate =
  (flip astrength && a ()) ||
  (flip bstrength && b ()) ||
  flip baserate;;

(* Chance of being caught at intersection #i given the time-step t *)
let being_caught i t () =
   (flip 0.5 && flip police_monitoring.(i)) ||
   (flip 0.3 && (if t < 3 then flip 0.2 else flip 0.4)) ||
   flip bad_luck;;

let game cheatingp () =
 let rec loop t pos =
   if pos >= n then t
   else 
   let red_light = flip 0.5 in
   if red_light then
      let cheat = flip cheatingp in
      if cheat then
         if at_least maxrisk true 
             (sample_importance dist_selector 10 (being_caught pos t))
         then fail () 			(* too much risk *)
         else loop (succ t) (succ pos)
      else loop (succ t) pos		(* we stay *)
   else loop (succ t) (succ pos)        (* we go on green light *)
 in loop 0 0
;;

let 
[(4.88281249999999485e-05, V 16); (0.01259765625, V 15);
 (0.0267578125, V 14); (0.053515625, V 13); (0.01328125, V 12);
 (0.0265625, V 11); (0.053125, V 10); (0.10625, V 9);
 (0.0249999999999999875, V 8); (0.049999999999999975, V 7);
 (0.09999999999999995, V 6)] =
sample_importance (random_selector 17) 10 (game 0.2);;

let [(0.010625, V 9); (0.01625, V 8); (0.0525, V 7); (0.025, V 6); (0.04, V 5)] =
sample_importance (random_selector 17) 50 (game 0.5);;


