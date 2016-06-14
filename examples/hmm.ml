(* A simple HMM model with a single hidden variable that has 8 states

  States represent position of a 1-dimensional random walk on 1..8

  State transition: one position to left/right with prob. 0.3 each;
  stay in state with prob. 0.4 (0.7 for boundary states)

  Observable: two states 'l' and 'r'. Prob. of observation=l in state
  k is 1-(k-1)/7

In all other implementations of the benchmark, the transition and
observation probabilities are tabulated. We won't use the close
formulas above either, to be realistic.

The other systems tabulate the transition and observation
probabilities in arrays -- sort of. The systems don't have arrays and
standard iterative operations on them, it seems, and so the encodings
are quite baroque and extensive (the latter is perhaps due to
`inlining' for the sake of performance). Primula encodes the states in
binary and has to define the transitions in terms of bits. That is
really quite unintuitive. In none of the other implementations the
code _clearly_ corresponds to the description of the problem. It is
not obvious at all that the implementation is correct.

It seems that of all the other systems, our expression of the model evolution 
and the formulation of the conditional query are the most straightforward.
The adequacy of our model encoding and of queries is obvious; that is
less obvious in the other benchmark implementations.

Another good comparison point of our implementation with the others:
how easy it is to extend the implementation, from 8 states to say, 64
states. In our implementation, just change a few constants
(specifically, state_max) and extend l_observation_prob. The latter
can be tabulated from a closed formula and so doesn't have to
be modified. The tabulation for transition_prob remains the same;
specifically, the evolution equation remains the same.
In other implementations, extension from 8 to 64 states requires
a lot of work. For example, in Primula, the file for 8-state model
multistatehmm8.rbn has the size of 3809 bytes,
whereas multistatehmm64.rbn has the size 39195 bytes. Roughly the same
expansion, by the order of magnitude, is observed for other implementations
(PRISM and Balios). In Primula, the generalization from 8 to 64 is quite
irregular, because of the peculiar binary encoding of states, in terms of
random bits.
*)

open Ptypes
open ProbM;;

type state = State of int;;		(* the valid range 1..8 *)
let state_min = State 1 and state_max = State 8;;
let from_state : state -> int = function State i -> i - 1;;
let to_state   : int -> state = fun i -> State (i+1);;
let nstates = from_state state_max - from_state state_min + 1;;

(* Tabulate the transition probabilities *)
(* We encode the sparse transition matrix compactly.
   In contrast, PRISM encodes the matrix in full, with all zeroes.
   In Primula, because of the binary encoding of the state and
   bit manipulations, the transition probability matrix is represented
   quite indirectly.
*)
let transition_prob = 
  Array.init nstates
  (fun i ->
    let st = to_state i in
    if st = state_min then [(0.7, st); (0.3, to_state (succ i))]
    else if st = state_max then [(0.7, st); (0.3, to_state (pred i))]
    else [(0.4, st); (0.3, to_state (succ i)); (0.3, to_state (pred i))]
  );;

(* observations *)
type obs = L | R;;
(* Tabulate the observation probabilities: of observing L *)
(* We use the numeric values directly from the Primula code *)
let l_observation_prob =
  [|1.0; 0.85714; 0.71428; 0.57142; 0.42857; 0.28571; 0.14285; 0.0|];;

(* The evolution function: compute the state for the next step *)
let evolve : state -> state = fun st ->
  dist (transition_prob.(from_state st));;

let observe : state -> obs = fun st ->
  let pl = l_observation_prob.(from_state st) in
  if pl = 0.0 then R else if pl = 1.0 then L else
  dist [(pl, L); (1. -. pl, R)];;

(* Queries *)
(* Run the model for N steps, asserting observations *)

let do_evolve n evidence =
  let st0 = to_state (uniform nstates) in
  let rec iter i n st =
    if i > n then st
    else let () = evidence st i in		(* check the evidence *)
         iter (succ i) n (evolve st)
  in iter 1 n st0
;;


(* The query: P(hiddenstate(10)|position(5)=left) *)
let query1 () = 
  do_evolve 10 (fun st -> function 5 -> if observe st <> L then fail () 
                                 | _ -> ());;

let tq1 = sample_importance (random_selector 17) 10000 query1;;

let  [(0.0195362930000001038, V (State 8));
      (0.0269278266099997332, V (State 7));
      (0.0393843397499996709, V (State 6));
      (0.0552575806799999805, V (State 5)); 
      (0.07079830065, V (State 4));
      (0.0876913622199998327, V (State 3));
      (0.0998305943399990792, V (State 2));
      (0.106255658350001794, V (State 1))] = tq1;;

let tq1' = snd (Inference.normalize tq1);;

let [(0.038633557681171285, V (State 8));
     (0.0532505190501595255, V (State 7));
     (0.0778836169925610361, V (State 6)); 
     (0.109273388279073416, V (State 5));
     (0.140005590205402181, V (State 4));
     (0.17341208490611959, V (State 3));
     (0.197417750889585131, V (State 2));
     (0.210123491995927891, V (State 1))] = tq1';;


(* Other systems report:

In Balios:

8 states: P(hiddenstate(10)|position(5)=left)=
[s1:0.21,s2:0.20,s3:0.19,s4:0.15,s5:0.11,s6:0.08,s7:0.05,s8:0.03]

In Primula
8 states: P(hiddenstate(10)|position(5)=left)=
[s1:0.2204,s2:0.2040,s3:0.1763,s4:0.1424,s5:0.1074,s6:0.0737,s7:0.046,s8:0.0298]
*)

(* Exact inference *)
(* I thought I needed variable elimination. It turns out, the exact
   result was computed just as fast as the sampling above. 
   The results of sampling 10000 times match those of the exact inference.
*)

let tq1_exact = exact_reify query1;;

let [(0.0195710406300005982, V (State 8));
     (0.0264436471037524448, V (State 7));
     (0.0387262008512519254, V (State 6));
     (0.0542304468099861214, V (State 5));
     (0.0707684496649872291, V (State 4)); 
     (0.086272791068737309, V (State 3));
     (0.0985554834162256921, V (State 2)); 
     (0.10542819045498758, V (State 1))] = tq1_exact;;

let tq1_exact' = snd (Inference.normalize tq1_exact);;

let [(0.0391423748278179676, V (State 8)); 
     (0.0528876908651939, V (State 7));
     (0.0774529825998843541, V (State 6));
     (0.108461707082790779, V (State 5));
     (0.141537960864701051, V (State 4)); 
     (0.172546876239070945, V (State 3));
     (0.197112445175818218, V (State 2)); 
     (0.210857962344722732, V (State 1))] = tq1_exact';;


(* ------------------------------------------------------------------------
   Investigating complexity and optimizing
*)

(* Let's check the complexity of our solution *)
let timeit = Inference.timeit;;

let queryn n () = 
  do_evolve n (fun st -> function 5 -> if observe st <> L then fail () 
                                 | _ -> ());;

let timet8 = timeit (fun () -> exact_reify (queryn 8));; (* 0.47 sec *)
let timet9 = timeit (fun () -> exact_reify (queryn 9));; (* 1.33 sec *)
let timet10 = timeit (fun () -> exact_reify (queryn 10));; (* 3.79 sec *)

(* That is not good: it looks like 3^n where n is the number of time
   steps in the evolution of the model.
*)

(* Let's look closer and profile the worker function *)

let counters = Array.make 12 0;;
let add_counters i =
  let i' =  if i >= Array.length counters then 0 else i
  in counters.(i') <- counters.(i') + 1;;

let do_evolve n evidence =
  let st0 = to_state (uniform nstates) in
  let rec iter i n st =
    add_counters(i);
    if i > n then st
    else let () = evidence st i in		(* check the evidence *)
         iter (succ i) n (evolve st)
  in iter 1 n st0
;;

let queryn n () = 
  do_evolve n (fun st -> function 5 -> if observe st <> L then fail () 
                                 | _ -> ());;

let _ = 
  Array.fill counters 0 (Array.length counters) 0;
  exact_reify (queryn 4);;
let [|0; 8; 22; 62; 176; 502; 0; 0; 0; 0; 0; 0|] = counters;;
(* 
 We clearly see the exponential behavior: factor of 3 as
 we advance i
*)

(* let us re-write from tail-recursive, so to, informally, infer backwards
   rather than forwards.
   We should make this dependence' on only the previous step explicit:
   We see the benefit soon.
*)

let do_evolve n evidence =
  let rec iter i =
    let new_st = 
      if i = 1 then to_state (uniform nstates)
      else
	let st = iter (pred i) in
	evolve st
    in let () = evidence new_st i in		(* check the evidence *)
    add_counters(i);
    new_st
  in iter n
;;

let queryn n () = 
  do_evolve n (fun st -> function 5 -> if observe st <> L then fail () 
                                 | _ -> ());;

let _ = 
  Array.fill counters 0 (Array.length counters) 0;
  exact_reify (queryn 4);;
let [|0; 8; 22; 62; 176; 0; 0; 0; 0; 0; 0; 0|] = counters;;
(*
 Seems like nothing changed. But we can eliminate variable now.
 Because surely the earlier variables can't depend on the earlier ones.
*)

let do_evolve n evidence =
  let rec iter i =
    let new_st = 
      if i = 1 then to_state (uniform nstates)
      else
	let st = variable_elim iter (pred i) in
	evolve st
    in let () = evidence new_st i in		(* check the evidence *)
    add_counters(i);
    new_st
  in iter n
;;

let queryn n () = 
  do_evolve n (fun st -> function 5 -> if observe st <> L then fail () 
                                 | _ -> ());;

let _ = 
  Array.fill counters 0 (Array.length counters) 0;
  exact_reify (queryn 4);;
let [|0; 8; 22; 22; 22; 0; 0; 0; 0; 0; 0; 0|] = counters;;
(* Now much better pattern *)

let tq1ve_exact = 
  Array.fill counters 0 (Array.length counters) 0;
  exact_reify (queryn 10);;

let [|0; 8; 22; 22; 22; 20; 20; 22; 22; 22; 22; 0|] = counters;;
(* This pattern persists *)

let [(0.0173481607499999975, V (State 8)); (0.02475776035, V (State 7));
     (0.0377869824625000073, V (State 6)); (0.0539469325375000058, V (State 5));
     (0.0710519301875, V (State 4)); (0.0872119927625000096, V (State 3));
     (0.100241383024999992, V (State 2)); (0.107651107924999989, V (State 1))]
    = tq1ve_exact;;

let tq1ve_exact' = snd (Inference.normalize tq1ve_exact);;

let [(0.0346965817243629279, V (State 8));
     (0.0495158920691905202, V (State 7));
     (0.0755745317339880096, V (State 6)); 
     (0.107894674285057141, V (State 5));
     (0.142104926161946199, V (State 4)); 
     (0.174425293714702861, V (State 3));
     (0.200484269682022598, V (State 2)); 
     (0.215303830628729681, V (State 1))] = tq1ve_exact';;

(* To remind, other systems report:

In Balios:

8 states: P(hiddenstate(10)|position(5)=left)=
[s1:0.21,s2:0.20,s3:0.19,s4:0.15,s5:0.11,s6:0.08,s7:0.05,s8:0.03]

In Primula
8 states: P(hiddenstate(10)|position(5)=left)=
[s1:0.2204,s2:0.2040,s3:0.1763,s4:0.1424,s5:0.1074,s6:0.0737,s7:0.046,s8:0.0298]
*)


let timet8 = timeit (fun () -> exact_reify (queryn 8));; (* 0 sec *)
let timet9 = timeit (fun () -> exact_reify (queryn 9));; (* 0 sec *)
let timet10 = timeit (fun () -> exact_reify (queryn 10));; 
   (* 0.003572 sec, in the compiled code: 0.003342 *)
let timet100 = timeit (fun () -> exact_reify (queryn 100));; 
   (* 0.034661 sec, in the compiled code: 0.03218 *)

(* That is a much better behavior *)
