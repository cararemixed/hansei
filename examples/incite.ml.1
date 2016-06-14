(*
   Coordination games and nested inference. Planning as inference
                         specifically

   Bounded-Rational Theory of Mind for Conversational Implicature

 Agent S tries to induce agent A to take a specific action. Agent S
 speaks to agent A and so communicates information that agent A uses to
 make decision. Agent S needs a model of agent's A mind so to predict
 how agent A can understand a particular utterance and how this
 understanding leads to a specific action.

 This example is intentionally very simple. We assume the language of
 agents is a single boolean formula (to be called the language
 formula) over two sorts of propositional variables: form variables
 and state variables. State variables describe the state of the
 world. They are `hidden' in a sense they cannot be communicated
 directly. Rather, in his utterance the speaker directly specifies a
 complete assignment to form variables (informally, in the natural
 language utterance, we can take the set of form variables is the set
 of all words in the natural language; a spoken phrase gives the
 assignment to the form variables, by setting the variables
 corresponding to the spoken words to true and the rest to false.)
 
 The state variables, the result of the communication, can be deduced
 by finding out which variables satisfy the language formula given a
 particular assignment to form variables. Generally, several assignments
 to state variables may satisfy the language formula.
 We assume a mapping from state variables and actions to
 utilities (which are real numbers). We assume that agent A takes the
 action that has the maximum expected utility in the set of the worlds
 that satisfies the language formula given the utterance (the
 assignments to form varaibles).  We assume agent S knows agent A's
 utility function. The agent S goal is to produce the utterance that
 maximizes the expected utility of a particular desired action.

 The nuance comes from the fact that computing the set of state
 variables that satisfy the language formula given the utterance is
 hard: it is the SAT problem. Therefore, agent A uses a particular
 _approximate_ SAT-solving algorithm; whose details thus influence the
 decision process of S. We assume that S knows the SAT-solving
 algorithm of A precisely. Thus S must do nested inference:
 determining the assignment to form variables relies on the the
 result of nested inference: determining mathematical expectation for
 the utility of a certain action.  

NOTE: explain this as a coordination game. Agents share the same goal,
the same utility function and aim to maximize the common utility.

This particular file implements the following example of scalar
implicature. Suppose a speaker and a hearer are arranging a party.
The speaker knows exactly how many of the invited people are coming to
the party and needs to tell the hearer a headcount so that the hearer
prepares an appropriate amount of food -- having too much food is bad,
but having too little food is much worse. The speaker may say the
precise number, a rough estimate such as (`all' (meaning all the
invited people), `some', `none'), or a more precise estimate (`some but not
all'). A more precise headcount report is more informative -- and so
may be harder to interpret. The speaker therefore has to balance the
benefits of precision with the risk of mis-interpretation. To estimate
these factors, the speaker needs to model the decision procedure of
the (bounded-rational) hearer: for each possible utterance, the
speaker should evaluate its likely interpretations by the hearer and
estimate how much food the hearer would buy. The speaker would chose
to say the phrase that induces the hearer to buy as much food as
needed, but not too much more.

Because we express probabilistic models and inference algorithms in
the same language, using the same primitive for random choice, it is
straightforward to represent how the speaker's probabilistic model
includes the hearer's decision making, in particular inference
algorithms the hearer might use.
*)

open Ptypes
open ProbM;;

type statev  = S_b0 | S_b1
type formv   = F_b0 | F_b1
type action  = A of int     (* How many pieces of food to buy: 0..3 *)
;;
type utility = float
;;
(* The value of the state variable in the current world *)
(* let vs state statev = List.member statev state;; *)

let utility state (A bought_food) = 
    let people_came = 
      (if state S_b0 then 1 else 0) +
      (if state S_b1 then 2 else 0) in
    - 10.0 *. float_of_int (abs(bought_food - people_came))
;;

let language form state =
  form F_b0 == state S_b0 &&
  form F_b1 == state S_b1;;

(* A random action *)
(* Since we do planning by inference, all `probabilities' are 1!
*)
let an_action () = 
  dist [(1.,A 0); (1.,A 1); (1.,A 2); (1.,A 3)];;


(* Agent A: accepts the assignment to form variables and
   determines how much food to buy.
   It chooses the action with the highest utility, or fails
*)
let agent_A_model form () =
  let s0 = letlazy (fun () -> flip 0.5) in
  let s1 = letlazy (fun () -> flip 0.5) in
  let state = function S_b0 -> s0 () | S_b1 -> s1 () in
  if not (language form state) then fail () else
  let action = an_action () in
  (utility state action, action)
;;

(* Max element of an non-empty array *)
(*
let argmax arr =
  let rec loop i (imax,vmax) =
    if i >= Array.length arr then imax 
    else let curr = arr.(i) in
    loop (succ i) (if curr >= vmax then (i,curr) else (imax,vmax))
  in loop 1 (0,arr.(0))
;;
*)

let ut1 = function F_b1 -> true | _ -> false;;

let 
  [(0.25, V (-0., A 2)); (0.25, V (-10., A 3)); (0.25, V (-10., A 1));
   (0.25, V (-20., A 0))] =
  exact_reify (agent_A_model ut1);;

let
  [(0.32, V (-0., A 2)); (0.28, V (-10., A 3)); (0.28, V (-10., A 1));
   (0.36, V (-20., A 0))] =
  sample_rejection (random_selector 17) 100 (agent_A_model ut1);;

(* Compute the max expected utility and the corresponding action
   The input is (utility * action) pV
   We compute weighted average of  utilities with the probabilities, 
   find actions
   We return 0, 1 or more maxima (0 maxima if the table is empty)
*)
let argmax plans =
  let pl = List.fold_left (fun pm (p,V (u,a)) ->
    PMap.insert_with (fun (x1,y1) (x2,y2) -> (x1+.x2, y1+.y2)) 
      a (u *. p, p) pm) (PMap.empty) plans in
  PMap.foldi (fun a (u,p) -> 
    let u = u /. p in
    function [] -> [(u,a)]
      | ((umax,_)::_) as acc -> 
	  if u > umax then [(u,a)] else
	  if u = umax then (u,a)::acc else acc) pl [];;

let [(-0., A 2)] = argmax (exact_reify (agent_A_model ut1));;

let inner_model inferencer form () =
 argmax (inferencer (agent_A_model form));;

(* The outer model *)
let agent_S_ideal_state = 
  function S_b1 -> true | _ -> false;; (* S knows 2 people come to the party *)

let agent_S_model inferencer () =
  let formvs = dist [(1.,[F_b1; F_b0]); (1.,[F_b1]);
		     (1.,[F_b0]); (1.,[]);] in
  let form fv = List.mem fv formvs in
  let action_A = match inner_model inferencer form () with
  | [(_,x)] -> x
  | [] -> A (uniform 4) (* If the hearer module produced nothing
			     assume the hearer will do something random *)
  | lst -> let len = List.length lst in (* several maxima, choose one *)
           let p = 1. /. float_of_int len in
           dist (List.map (fun (_,x) -> (p,x)) lst) 
  in (utility agent_S_ideal_state action_A, formvs)
;;

let [(1., V (-0., [F_b1])); (1., V (-10., [F_b1; F_b0])); (1., V (-10., [F_b0]));
     (1., V (-20., []))] =
exact_reify (agent_S_model (fun m -> exact_reify m));;

let
[(0.25, V (-0., [F_b1; F_b0])); (0.25, V (-0., [F_b1]));
 (0.25, V (-0., [F_b0])); (0.25, V (-0., [])); 
 (0.5, V (-10., [F_b1; F_b0]));
 (0.5, V (-10., [F_b1])); (0.5, V (-10., [F_b0])); (0.5, V (-10., []));
 (0.25, V (-20., [F_b1; F_b0])); (0.25, V (-20., [F_b1]));
 (0.25, V (-20., [F_b0])); (0.25, V (-20., []))] =
exact_reify (agent_S_model (fun m -> sample_rejection dist_selector 1 m));;

(* Since rejection sampling of 1 just returns a random action, it doesn't matter
   what the speaker says.
*)

let 
[(0.25390625, V (-0., [F_b1; F_b0])); (0.26171875, V (-0., [F_b1]));
 (0.25, V (-0., [F_b0])); (0.24609375, V (-0., []));
 (0.5078125, V (-10., [F_b1; F_b0])); (0.5, V (-10., [F_b1]));
 (0.5, V (-10., [F_b0])); (0.4921875, V (-10., []));
 (0.23828125, V (-20., [F_b1; F_b0])); (0.23828125, V (-20., [F_b1]));
 (0.25, V (-20., [F_b0])); (0.26171875, V (-20., []))] =
exact_reify (agent_S_model (fun m -> sample_rejection dist_selector 2 m));;

(* But when the hearer uses two samples, it pays, by 1%, to tell the truth. *)


(* More complex model: some-all game *)
type statev  = S_b0 | S_b1 | S_conj
type formv   = F_all | F_some | F_notall | F_none
;;

let utility state (A bought_food) = 
    let people_came = 
      (if state S_b0 then 1 else 0) +
      (if state S_b1 then 2 else 0) in
    - 10.0 *. float_of_int (abs(bought_food - people_came))
;;


let int_of_bit = function true -> 1 | false -> 0
;;

let language form state =
  (if (int_of_bit (form F_all) +
      int_of_bit (form F_some) +
      int_of_bit (form F_notall) +
      int_of_bit (form F_none) > 1) then state S_conj else true)
  &&
  let people_came = 
    (if state S_b0 then 1 else 0) +
      (if state S_b1 then 2 else 0) in
  (if form F_all then people_came == 3 else true) &&
  (if form F_some then people_came > 0 else true) &&
  (if form F_notall then people_came < 3 else true) &&
  (if form F_none then people_came == 0 else true);;

let agent_A_model form () =
  let s0 = letlazy (fun () -> flip 0.5) in
  let s1 = letlazy (fun () -> flip 0.5) in
  let sc = letlazy (fun () -> flip 0.5) in
  let state = function S_b0 -> s0 () | S_b1 -> s1 () | S_conj -> sc () in
  if not (language form state) then fail () else
  let action = an_action () in
  (utility state action, action)
;;

let ut1 = function F_some -> true | _ -> false;;

let
[(0.25, V (-0., A 3)); (0.25, V (-0., A 2)); (0.25, V (-0., A 1));
 (0.25, V (-10., A 3)); (0.5, V (-10., A 2)); (0.25, V (-10., A 1));
 (0.25, V (-10., A 0)); (0.25, V (-20., A 3)); (0.25, V (-20., A 1));
 (0.25, V (-20., A 0)); (0.25, V (-30., A 0))] =
  exact_reify (agent_A_model ut1);;

let inner_model inferencer form () =
 argmax (inferencer (agent_A_model form));;

(* Note the weighted utility *)
let [(-6.66666666666666696, A 2)] = argmax (exact_reify (agent_A_model ut1));;

let ut2 = function F_some -> true | F_notall -> true | _ -> false;;

let 
[(0.125, V (-0., A 2)); (0.125, V (-0., A 1)); (0.125, V (-10., A 3));
 (0.125, V (-10., A 2)); (0.125, V (-10., A 1)); (0.125, V (-10., A 0));
 (0.125, V (-20., A 3)); (0.125, V (-20., A 0))] =
exact_reify (agent_A_model ut2);; 

let [(-5., A 2); (-5., A 1)] = argmax (exact_reify (agent_A_model ut2));;

(* The outer model *)
let agent_S_ideal_state = 
  function S_b1 -> true | _ -> false;; (* S knows 2 people come to the party *)

let all_forms = 
  let bit0 n = n mod 2 == 1 in
  let bit1 n = n / 2 mod 2 == 1 in
  let bit2 n = n / 4 mod 2 == 1 in
  let bit3 n = n / 8 mod 2 == 1 in
  let rec loop i =
    if i > 15 then [] else
   ((if bit0 i then [F_all] else []) @
      (if bit1 i then [F_some] else []) @
      (if bit2 i then [F_notall] else []) @
      (if bit3 i then [F_none] else []) @ []) :: loop (succ i)
  in loop 0;;

let agent_S_model inferencer () =
  let formvs = dist (List.map (fun v -> (1., v)) all_forms) in 
  let form fv = List.mem fv formvs in
  let action_A = match inner_model inferencer form () with
  | [(_,x)] -> x
  | [] -> A (uniform 4) (* If the hearer module produced nothing
			     assume the hearer will do something random *)
  | lst -> let len = List.length lst in (* several maxima, choose one *)
           let p = 1. /. float_of_int len in
           dist (List.map (fun (_,x) -> (p,x)) lst) 
  in (utility agent_S_ideal_state action_A, formvs)
;;

let
[(0.25, V (-0., [F_some; F_none]));
 (0.25, V (-0., [F_some; F_notall; F_none]));
 (0.5, V (-0., [F_some; F_notall])); (1., V (-0., [F_some]));
 (0.25, V (-0., [F_all; F_none]));
 (0.25, V (-0., [F_all; F_notall; F_none]));
 (0.25, V (-0., [F_all; F_notall]));
 (0.25, V (-0., [F_all; F_some; F_none]));
 (0.25, V (-0., [F_all; F_some; F_notall; F_none]));
 (0.25, V (-0., [F_all; F_some; F_notall])); (0.5, V (-0., []));
 (1., V (-10., [F_notall])); (0.5, V (-10., [F_some; F_none]));
 (0.5, V (-10., [F_some; F_notall; F_none]));
 (0.5, V (-10., [F_some; F_notall])); (0.5, V (-10., [F_all; F_none]));
 (0.5, V (-10., [F_all; F_notall; F_none]));
 (0.5, V (-10., [F_all; F_notall]));
 (0.5, V (-10., [F_all; F_some; F_none]));
 (0.5, V (-10., [F_all; F_some; F_notall; F_none]));
 (0.5, V (-10., [F_all; F_some; F_notall])); (1., V (-10., [F_all; F_some]));
 (1., V (-10., [F_all])); (0.5, V (-10., [])); (1., V (-20., [F_none]));
 (1., V (-20., [F_notall; F_none])); (0.25, V (-20., [F_some; F_none]));
 (0.25, V (-20., [F_some; F_notall; F_none]));
 (0.25, V (-20., [F_all; F_none]));
 (0.25, V (-20., [F_all; F_notall; F_none]));
 (0.25, V (-20., [F_all; F_notall]));
 (0.25, V (-20., [F_all; F_some; F_none]));
 (0.25, V (-20., [F_all; F_some; F_notall; F_none]));
 (0.25, V (-20., [F_all; F_some; F_notall]))] =
exact_reify (agent_S_model (fun m -> exact_reify m));;

let [(-0., [F_some])] =
argmax (exact_reify (agent_S_model (fun m -> exact_reify m)));;

let [(-8.90625, [F_some])] =
argmax (exact_reify 
(agent_S_model (fun m -> sample_rejection dist_selector 2 m)));;

(* Asymmetric utility *)

let utility state (A bought_food) = 
    let people_came = 
      (if state S_b0 then 1 else 0) +
      (if state S_b1 then 2 else 0) in
    - 10.0 *. float_of_int (
       let diff = bought_food - people_came in
       if diff = 0 then 0 else
       if diff > 0 then diff else 10*(-diff))
;;

let agent_A_model form () =
  let s0 = letlazy (fun () -> flip 0.5) in
  let s1 = letlazy (fun () -> flip 0.5) in
  let sc = letlazy (fun () -> flip 0.5) in
  let state = function S_b0 -> s0 () | S_b1 -> s1 () | S_conj -> sc () in
  if not (language form state) then fail () else
  let action = an_action () in
  (utility state action, action)
;;

let ut1 = function F_some -> true | _ -> false;;

let
[(0.25, V (-0., A 3)); (0.25, V (-0., A 2)); (0.25, V (-0., A 1));
 (0.25, V (-10., A 3)); (0.25, V (-10., A 2)); (0.25, V (-20., A 3));
 (0.25, V (-100., A 2)); (0.25, V (-100., A 1)); (0.25, V (-100., A 0));
 (0.25, V (-200., A 1)); (0.25, V (-200., A 0)); (0.25, V (-300., A 0))] =
  exact_reify (agent_A_model ut1);;

let inner_model inferencer form () =
 argmax (inferencer (agent_A_model form));;

(* Note the weighted utility *)
let [(-10., A 3)] = argmax (exact_reify (agent_A_model ut1));;

let ut2 = function F_some -> true | F_notall -> true | _ -> false;;

let 
[(0.125, V (-0., A 2)); (0.125, V (-0., A 1)); (0.125, V (-10., A 3));
 (0.125, V (-10., A 2)); (0.125, V (-20., A 3)); (0.125, V (-100., A 1));
 (0.125, V (-100., A 0)); (0.125, V (-200., A 0))] =
exact_reify (agent_A_model ut2);; 

let [(-5., A 2)] = argmax (exact_reify (agent_A_model ut2));;

(* The outer model *)
let agent_S_ideal_state = 
  function S_b1 -> true | _ -> false;; (* S knows 2 people come to the party *)

let agent_S_model inferencer () =
  let formvs = dist (List.map (fun v -> (1., v)) all_forms) in 
  let form fv = List.mem fv formvs in
  let action_A = match inner_model inferencer form () with
  | [(_,x)] -> x
  | [] -> A (uniform 4) (* If the hearer module produced nothing
			     assume the hearer will do something random *)
  | lst -> let len = List.length lst in (* several maxima, choose one *)
           let p = 1. /. float_of_int len in
           dist (List.map (fun (_,x) -> (p,x)) lst) 
  in (utility agent_S_ideal_state action_A, formvs)
;;

(*
exact_reify (agent_S_model (fun m -> exact_reify m));;
*)

let [(-0., [F_notall]); (-0., [F_some; F_notall])] =
argmax (exact_reify (agent_S_model (fun m -> exact_reify m)));;

let [(-60.078125, [F_some]); (-60.078125, [])] =
argmax (exact_reify 
(agent_S_model (fun m -> sample_rejection dist_selector 2 m)));;

let [(-5.31250000000000089, [F_all])] =
argmax (sample_importance (random_selector 17) 100 
(agent_S_model (fun m -> sample_rejection dist_selector 10 m)));;

let [(-15.9212239583333304, [F_some])] =
argmax (sample_importance (random_selector 17) 1000 
(agent_S_model (fun m -> sample_rejection dist_selector 10 m)));;

let [(-0., [F_notall])] =
argmax (exact_reify
(agent_S_model (fun m -> sample_importance dist_selector 2 m)));;
