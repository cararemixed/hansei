(*
 An illustration of non-deterministic programming

 Our example is the following puzzle, which I received from a friend
 of mine back in 1998.
> Think laterally and you'll get it in about thirty seconds. Think logically
> and you hit a brick wall!
>
> Here's a good test for intelligent minds.  There are two answers,
> neither of which are trick answers. Allegedly, this is one of the
> questions for potential Microsoft employees.
> Some people really get caught up trying to solve this problem.
> Reportedly, one guy solved it by writing a C program, although that took
> him 37 minutes to develop (compiled and ran on the 1st try  though).
> Another guy solved it in three minutes. A group of 50, at Motorola,
> couldn't  figure it out at all. See how long it takes you.
> Here we go...
>
> "U2" has a concert that starts in 17 minutes and they must all cross a
> bridge to get there.  All four men begin on the same side of the
> bridge.  It is night. There is one flashlight.  A maximum of two people
> can cross at one time.  Any party who crosses, either 1 or 2 people,
> must have the flashlight with them. The flashlight must be walked back
> and forth, it cannot be thrown, etc..  Each band member walks at a
> different speed.  A pair must walk together at the rate of the slower
> man's pace:
>
> Bono:  1 minute to cross
> Edge:  2 minutes to cross
> Adam:  5 minutes to cross
> Larry: 10 minutes to cross
>
> For example: if Bono and Larry walk across first, 10 minutes have
> elapsed when they get to the other side of the bridge.  If Larry then
> returns with the flashlight, a total of 20 minutes have passed and you
> have failed the mission.
>
> Notes: There is no trick behind this.  It is the simple movement of
> resources in the appropriate order. There are two known answers to this
> problem.
>
> Note: Microsoft expects you to answer this question in under 5 minutes!

*)

(* #load "unix.cma";;
   #load "prob.cma";;
*)

open Printf;;

(* To solve the puzzle, we use a library of non-deterministic
   functions with the following simple interface.
   We assume that the non-deterministic computation to run
   would print out its result when it finishes. Therefore,
   its return type, and the return type of run are both units.
*)
module type SimpleNonDet = sig
    (* choose one element from a list *)
    val choose : 'a list -> 'a
    val run : (unit -> unit) -> unit
end;;

(* One implementation of SimpleNonDet: using Unix fork *)
(* We can watch processes created and dying *)
module Fork : SimpleNonDet = struct
  open Unix

  let rec choose = function
    | []     -> exit 666
    | [x]    -> x
    | (h::t) -> 
	let pid = fork () in
	if pid = 0 then h
	(* Throttle parallelism *)
	(* without wait, too many processes launched; OS can't handle them *)
	else let _ = wait () in 
	choose t

  let run m =
    match fork () with
    | 0 -> m (); printf "Solution found\n"; exit 0
    | _ -> 
	begin
	  try while true do waitpid [] 0 done
	  with | Unix_error (ECHILD,_,_) -> 
	    Printf.printf "Done"
	    | e -> 
		Printf.printf "Problem: %s\n" (Printexc.to_string e)
	end
end;;

(* Another implementation, using Hansei *)
module Hansei : SimpleNonDet = struct
  open ProbM;;
  let choose = function
    | [] -> fail ()
    | xs -> uniformly (Array.of_list xs)
  let run m = ignore (exact_reify m)
end;;

(*
open Hansei;;
*)

open Fork;;

(* Fail the computation *)
let fail () = choose [];;

(* Solution to the puzzle *)

(* Band members *)
type u2 = Bono | Edge | Adam | Larry;;

let speed = function
  | Bono  -> 1
  | Edge  -> 2
  | Adam  -> 5
  | Larry -> 10;;

let string_name = function
  | Bono  -> "Bono"
  | Edge  -> "Edge"
  | Adam  -> "Adam"
  | Larry -> "Larry"
;;

let print_names oc = function
  | [] -> fprintf oc "[]"
  | (h::t) -> fprintf oc "[%s%a]" (string_name h)
	        (fun oc -> List.iter (fun x -> fprintf oc ", %s" (string_name x))) t
;;

(* List of band members on one side of the bridge *)
type side = u2 list;;


(* Selecting one or two people to cross to the other side *)
let select_party side =
  let p1 = choose side in
  let p2 = choose (List.filter (fun x -> x >= p1) side) in
  if p1 = p2 then [p1] else [p1;p2]
;;

(* computing the time for the party to cross the bridge *)
let elapsed_time = 
  List.fold_left (fun z x -> max z (speed x)) 0;;

(* Set subtraction *)
let without l =
  List.filter (fun x -> not (List.mem x l));;

let rec print_trace trace =
  List.iter (function (people,dir) ->
    printf "%s: %a\n" (if dir then "forward" else "back") print_names people)
  trace;
  printf "\n"
;;


(* The main function, accumulating the solution in the 'trace',
   which lists the name of people crossing the bridge and the
   direction.
   The last argument of the function is (side * side),
   describing the people on both sides of the bridge
*)
let rec loop trace forward time_left = function
  | ([], _) when forward  ->       (* nobody is on the original side *)
      print_trace (List.rev trace)
  | (_, []) when not forward  ->   (* ditto *)
      print_trace (List.rev trace)
  | (side_from, side_to) ->
      let party   = select_party side_from in
      let elapsed = elapsed_time party in
      let _ = if elapsed > time_left then fail () in
      let side_from' = without party side_from in
      let side_to'   = side_to @ party in
      loop ((party,forward)::trace) (not forward) (time_left - elapsed)
	(side_to',side_from')
;;

run (fun () -> loop [] true 17 ([Bono;Edge;Adam;Larry],[]));;

(* Two solutions are printed *)
