(* Probabilistic embedded domain specific language *)

(* Tests of exact inference and the comparison of the syntax with that of IBAL*)

open Ptypes;;
open ProbM;;


(* ------------------------------------------------------------------------
 * Basic tests 
 *)

(* illustration of sharing/nonsharing: flip twice and `and' the results *)

let tflip2_shared () =   (* sharing of flips *)
  let v = flip 0.5 in
  v && v;;
let [(0.5, V true); (0.5, V false)] = exact_reify tflip2_shared;;

(* reify: done; 2 accepted 0 rejected 0 left
*)

let tflip2_noshared () =   (* independent flips *)
  flip 0.5 && flip 0.5;;
let [(0.25, V true); (0.75, V false)] = exact_reify tflip2_noshared;;
(* Result:
reify: done; 3 accepted 0 rejected 0 left
*)

let talarm () =
  let earthquake = flip 0.01 and burglary = flip 0.1 in
  if earthquake 
     then if burglary then flip 0.99 else flip 0.2
     else if burglary then flip 0.98 else flip 0.01
;;
let () = assert (
  exact_reify talarm
  = [(0.108720000000000011, V true); (0.891280000000000072, V false)]);;
(* reify: done; 8 accepted 0 rejected 0 left *)

(* The famous sprinkle example:  given that the grass is wet on a given
   day, did it rain or did the sprinkler come on?
   This is the basic model for one single day, just for the sake
   of introducing our library. More general models are considered in
   slazy.ml
*)

let grass_model () =
 let rain = flip 0.3 and sprinkler = flip 0.5 in
 let grass_is_wet = 
   (flip 0.9 && rain) || (flip 0.8 && sprinkler) || flip 0.1 in
 if not grass_is_wet then fail ();
 rain;;

let [(0.2838, V true); (0.321999999999999897, V false)] =
  exact_reify grass_model;;
(* 14 worlds are examined *)

(* Tests of library distributions *)

let [(0.125, V 8); (0.125, V 7); (0.125, V 6); (0.125, V 5); (0.125, V 4);
     (0.125, V 3); (0.125, V 2); (0.125, V 1)] =
  exact_reify (fun () -> uniform_range 1 8);;

(* Tests of the geometric distribution: exact inference to a specific
   depth. *)
let [(0.00286875000000000107, V 3); (0.0191250000000000031, V 2); (0.1275, V 1);
     (0.85, V 0); (1.13906250000000092e-05, C _);
     (6.45468750000000426e-05, C _); (0.000430312500000000248, C _)] =
  Inference.explore (Some 4) (reify0 (fun () -> geometric 0.85));;

let 
 [(1.4523050597099037e-06, V 7); (9.68203373139935684e-06, V 6);
  (6.45468915426623699e-05, V 5); (0.000430312610284415691, V 4);
  (0.00286875073522943743, V 3); (0.0191250049015295812, V 2);
  (0.127500032676863856, V 1); (0.850000217845759, V 0)] =
  exact_reify (fun () -> geometric_bounded 7 0.85);;



(* ------------------------------------------------------------------------
 * Tests from IBAL, to compare the syntax of IBAL with our EDSL 
 *)

(* foo.ibl, program 1
  // P(e) = 0.6; P(TT) = 1.0
  obs { y : _, z : true } in
  let x = dist [ 0.6 : true, 0.4 : false ] in
  let y = x in
  let z = x in
  ({ y = y, z = z })
*)

let tfooibl1 () = 
  observe (fun (_,z) -> z = true)
  (fun () ->
    let x = flip 0.6 in
    let y = x in
    let z = x in (y,z));;

let () = assert (
          (exact_reify tfooibl1)
    = [(0.6, V (true,true))]);;
(*
 reify: done; 1 accepted 1 rejected 0 left
 val rtfooibl1 : unit pV = PV [(0.6, V ())]
*)

(* foo.ibl, program 2
  // P(e) = 1; P(d,e) = 0.2; P(c,e) = 0.48; P(b,e) = 0.32
  { fst = let x = 'a in
   let f(x,y) =
      if dist [ 0.2 : true, 0.8 : false ] then x else y
      in f('d, dist [ 0.4 : 'b, 0.6 : 'c ]), 
   snd = 'e }
*)
(* Note how similar the syntaxes are. The results match, too *)
let tfooibl2 () = 
  (let x = 'a' in
   let f (x,y) =
     if dist [ (0.2,true); (0.8,false)] then x else y
     in f('d', dist [ (0.4,'b'); (0.6,'c') ]), 
   'e');;

let () = assert (
          (exact_reify tfooibl2)
    = [(0.2, V ('d', 'e')); (0.48, V ('c', 'e'));
       (0.320000000000000062, V ('b', 'e'))]);;
(*       reify: done; 4 accepted 0 rejected 0 left *)

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
          (exact_reify tfooibl3)
    = [(0.25, V true)]);;
(* reify: done; 2 accepted 2 rejected 0 left *)

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

let () = assert (
          (exact_reify tiblt2)
    = [(0.021, V true); (0.00900000000000000105, V false)]);;

(* reify: done; 4 accepted 1 rejected 0 left *)

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
 dist [ (0.8, f); (0.2, g) ] ());;

let () = assert (
          (exact_reify tmusictr41)
    = [(0.14, V true)]);;
(* reify: done; 2 accepted 2 rejected 0 left *)

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

let () = assert (
          (exact_reify tmusictr42)
    = [(0.003, V true); (0.00699999999999999928, V false)]);;

(* reify: done; 2 accepted 1 rejected 0 left *)




(* ------------------------------------------------------------------------
 * Reflection and reification: how to express early world collapse
   and optimize computations
 *)

(* The exact_reify is not too naive, which is can be seen from the
   result of tflip2_noshared already. The following test makes the optimality
   (sophistication) clearer.

   We evaluate AND of ten flips
*)

let flips_and n () = 
  let rec loop n = 
    if n = 1 then flip 0.5
       else flip 0.5 && loop (n-1)
  in loop n;;
let rtflips_10and = exact_reify (flips_and 10);;
(*
reify: done; 11 accepted 0 rejected 0 left
val rtflips_10and : bool pV =
  PV [(0.0009765625, V true); (0.9990234375, V false)]
*)

(* Naively, we would have thought we needed to evaluate 2^10 of possible
   worlds: each (nested) flip splits the world. But as the result
   shows, we managed with only 10+1 worlds. The reason is that the
   algorithm is NOT tail recursive, and && is a _special_ form
   rather than a function. That is, when flip 0.5 yields false, we no
   longer need to evaluate loop (n-1). We finish right away.
   It is imperative that we write [flip 0.5 && loop (n-1)]
   rather than [loop (n-1) && flip 0.5].

   Such an optimality (exponential reduction) came from the fact that
   we started to collapse worlds early.  Ostensibly, the algorithm
   collapses worlds only when we finished evaluating it -- when it is too
   late. Ideally, we should see if two worlds in progress are the same --
   but that requires us to (extensionally!) compare continuations --
   which seems impossible. In the case above, the comparsion of 
   the continuations and collapse happened implicitly, due to the
   special _control_ structure of the algorithm: (false && k)
   yields false regarding of the continuation. Thus evaluation
   of that _control structure_ embodies the collapse of all worlds
   represented by k.

   But the same trick won't work if we want to compute XOR of ten flips.
   XOR really needs the values of its two arguments in order to proceed.

   One, neatest, solution to the early collapse is suggested by Ken. 
   He essentially showed the way to _intensionally_ compare two continuations.
   Indeed, in our case, the continuations result from splitting the current
   world. One continuation receives 'true' and another receives 'false'.
   So, the two worlds differ *only* in the value of the variable that receives
   the result of the flip. If that variable is garbage collected, then
   the difference between worlds disappears and we can collapse the
   worlds in progress. Again, the _intension_ of the world (continuation)
   is the value of its flips and derived quantities. If we can combine
   the value of the flips and forget about the original flips, two worlds
   become intensionally equal and so can be collapsed into one.

   It seems however that solution, in some circumstances, may have
   a dual. Dual in a sense like CBV is dual to CBN.
   Variable is a continuation, and garbage collection is done
   by `region management'. The solution is again _non_ tail recursive.
   The solution critically relies on our ability to reify and reflect
   the probilistic monadic computations. Here we truly need delimited
   continuations.
*)

let xor (x:bool) y = x <> y;;

(* First, the naive evaluation of the xor of 10 flips *)
let flips_xor n () = 
  let rec loop n = 
    if n = 1 then flip 0.5
       else xor (flip 0.5) (loop (n-1))
  in loop n;;
let rtflips_10xor = exact_reify (flips_xor 10);;
(*
reify: done; 1024 accepted 0 rejected 0 left
val rtflips_10xor : bool pV = PV [(0.5, V true); (0.5, V false)]
*)

(* The above was naive: we indeed had to evaluate 512+512 possible
   worlds. Here is an optimal xor
*)

let flips_xor' n () = 
  let rec loop n = 
    if n = 1 then flip 0.5
       else let r = reflect (exact_reify (fun () -> loop (n-1)))
            in xor (flip 0.5) r
  in loop n;;
let [(0.5, V true); (0.5, V false)] = exact_reify (flips_xor' 10);;
(*
reify: done; 2 accepted 0 rejected 0 left
reify: done; 4 accepted 0 rejected 0 left
reify: done; 4 accepted 0 rejected 0 left
reify: done; 4 accepted 0 rejected 0 left
reify: done; 4 accepted 0 rejected 0 left
reify: done; 4 accepted 0 rejected 0 left
reify: done; 4 accepted 0 rejected 0 left
reify: done; 4 accepted 0 rejected 0 left
reify: done; 4 accepted 0 rejected 0 left
reify: done; 4 accepted 0 rejected 0 left
*)

(* That is obviously better: we needed only 38 threads to do the job.
   The 'let' operator is important, for `sharing': we needed
   to compute the join in the original thread, so we can share the result
   among the childrens, after the flip.
*)
