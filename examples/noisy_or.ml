(*
``Noisy-or model: A very basic model that uses the noisy-or function
for combining several causal inputs. Input structures are directed
acyclic graphs on which a random unary attribute is propagated from the
roots downward.  Reference model comes from Primula.''
   http://www.cs.aau.dk/~jaeger/plsystems/models.html

This problem emphasizes memoization of random functions.

In Primula the model looks very simple (partly because noisy-or
is built-in):

    @root(v)=sformula(root(v));
    @norform(v)=n-or{(on(w):0.8,0.1)|w:edge(w,v)};

    on(v)=(@root(v):0.5,@norform(v));
with an additional file specifying the parameters
    DOMAIN: {0, 1, 2, 3, 4};
    COORDINATES: {(95,53) (81,140) (159,116) (177,220) (229,55)};
    RELATION: root/1 color -28416 {0 4};
    RELATION: edge/2 color -4613316 {(0,2) (0,1) (1,3) (2,3) (4,2) (4,3)};

I'm not sure what color or COORDINATES mean -- probably some internal
tuning or presentation parameters.  The PRISM implementation has no
mentioning of COORDINATES or color or their values.

*)

open Ptypes
open ProbM;;

(* Specify the parameters of the problem -- in the syntax that
   resembles that of Primula 
*)
let roots = [0; 4];;
let edges = [(0,2);(0,1);(1,3);(2,3);(4,2);(4,3)];;


let root_prob = 0.5;;
let edge_prob = 0.8;;
let leak_prob = 0.1;;

(* Before we get to the generic model, we reproduce the PRISM solution
   to the benchmark. The graph is built into the model, which propagates
   the random value from the roots through the nodes.
   Our code is far shorter than that of PRISM since PRISM emulates
   applicative code in a logical programming language. That is always
   ungainly.
*)
let model_fwd () =
   let rec noisy_or = function [] -> false
   | (h::t) -> (if h then flip edge_prob else flip leak_prob) || noisy_or t in
   let (n0,n4) = (flip root_prob,flip root_prob) in
   let n1 = noisy_or [n0] in
   let n2 = noisy_or [n0;n4] in
   let n3 = noisy_or [n1;n2;n4]
   in n3
;;
let qfwd = exact_reify model_fwd;;
let [(0.81441875000000008, V true); (0.185581250000000031, V false)] =
   qfwd;;
(* Prism computes: P(on(3))=0.81 *)

(* We'd like to do better: to abstract away the particular graph and
   do the backward propagation. We don't need to know the values in the
   nodes that don't contribute to the node of interest. We start with the
   node of interest, and work our way backwards. But we have to mind
   sharing! As we work backwards, we may encounter a given node several times.
   Each time the value of the random parameter must be the same.
   Fortunately, our system has a built-in memoization predicate.
*)

(* The rest is generic *)

(* Process the list of edges and build for each node the set of its
   predecessors
*)
module M = PMap

let predecessors = 
  let add_edge m (vf,vt) = M.insert_with (@) vt [vf] m in
  List.fold_left add_edge M.empty edges;;

(* The following model lets the user assert the available evidence:
   the argument evidence of the type int -> bool option.
   Given a vertex v, the function should return (Some e) if there
   is observation e for the vertex v. If there is no evidence, the
   function should return None.

   Unlike the PRISM implementation (and like Primula and Balios, it seems)
   we reason backwards, from the given node backwards along the edges
   until we get to the roots. We must use memoization to account
   for sharing in the graph.

*)

let rec member v = function [] -> false | (v'::t) -> v = v' || member v t;;

(* Memoizing fix-point combinator. Alas, we can't use let rec as in
let fixm f = let rec g = memo (fun v -> f g v) in g;;

  because of the error "This kind of expression is not allowed as 
  right-hand side of `let rec'"

There are always work-arounds, fortunately.
*)

let fixm f = 
   let self = ref (fun v -> failwith "blackhole") in
   let g = memo (fun v -> f !self v) in
   self := g; g
;;

(* There was another problem: our memo could not memoize recursive
   functions (which recursively call the memoized functions).
   Also, the memoization table used by our internal memo is not
   very efficient...
   But the improved and faster memo can memozie the recursive functions,
   so the example does work now.
*)

let model (v:int) (evidence : int -> bool option) =
  let loop self v = 
  match evidence v with
  | Some v -> v
  | None -> 
      if member v roots then flip root_prob
      else 				(* computing noisy OR over ws *)
	let ws = M.find v predecessors in
	let rec noisy_or = function 
	  | [] -> false
	  | (w::ws) -> 
	      (if self w then flip edge_prob else flip leak_prob)
	      || noisy_or ws
	in noisy_or ws
   in fixm loop v
;;
(* Unconditional query: P(on(3)) *)
let tq1m = exact_reify (fun () -> model 3 (fun _ -> None));;
let [(0.81441875000000008, V true); (0.185581250000000031, V false)]
   = tq1m;;
(* All other systems infer P(on(3))=0.81.
*)

(* In this model, the user supplies evidence as the (partly filled)
   memoization table: a mapping from nodes to booleans.
*)
let model (v:int) (evidence : (int,bool) M.t) =
  let rec loop evidence v = 
  let record evidence vl = (vl,M.add v vl evidence) in
  try (M.find v evidence,evidence) 
  with Not_found ->
      if member v roots then record evidence (flip root_prob)
      else 				(* computing noisy OR over ws *)
	let ws = M.find v predecessors in
	let rec noisy_or ev = function 
	  | [] -> record ev false
	  | (w::ws) -> 
	      let (vlw,ev) = loop ev w in
              let vl = if vlw then flip edge_prob else flip leak_prob in
              if vl then record ev vl else noisy_or ev ws
	in noisy_or evidence ws
   in fst (loop evidence v)
;;
 
(* Unconditional query: P(on(3)) *)
let tq1 = exact_reify (fun () -> model 3 M.empty);;

let [(0.81441875000000008, V true); (0.185581250000000031, V false)]
    = tq1;;

(* All other systems infer P(on(3))=0.81.
*)


(* Conditional query: P(on(3)|!on(0)) *)
let tq2 = exact_reify (fun () -> model 3 (M.add 0 false M.empty));;

let [(0.6864675, V true); (0.313532500000000047, V false)]
    = tq2;;

(* Primula and Balios give P(on(3)|!on(0))=0.67 
   In both of these systems, noisy-or is built-in. I don't know what
   exactly it does.
*)

(* It turns out, we can even handle a larger model with 19 vertices. *)

let roots = [0; 1; 2; 3];;
let edges = [(0,4);(0,5);(1,5);(1,6);(2,6);(3,7);(3,8);(8,13);
	     (8,16);(12,13);(7,12);(6,7);(5,6);(5,9);(4,10);(4,11);
	     (9,10);(10,11);(11,18);(18,19);(11,19);(17,19);(13,14);(14,15);
	     (16,17);(13,16);(14,17);(17,18);(15,18);(9,12);(9,15);(12,15)];;

let predecessors = 
  let add_edge m (vf,vt) = M.insert_with (@) vt [vf] m in
  List.fold_left add_edge M.empty edges;;

let model (v:int) (evidence : (int,bool) M.t) =
  let rec loop evidence v = 
  let record evidence vl = (vl,M.add v vl evidence) in
  try (M.find v evidence,evidence) 
  with Not_found ->
      if member v roots then record evidence (flip root_prob)
      else 				(* computing noisy OR over ws *)
	let ws = M.find v predecessors in
	let rec noisy_or ev = function 
	  | [] -> record ev false
	  | (w::ws) -> 
	      let (vlw,ev) = loop ev w in
              let vl = if vlw then flip edge_prob else flip leak_prob in
              if vl then record ev vl else noisy_or ev ws
	in noisy_or evidence ws
   in fst (loop evidence v)
;;

(* Unconditional query: P(on(15)) *)
let tq1l = exact_reify (fun () -> model 15 M.empty);;
let [(0.901446179820137083, V true); (0.0985538201798756, V false)]
    = tq1l;;
