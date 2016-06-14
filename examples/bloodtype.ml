(* Bloodtype benchmark *)

(* re-writing of the PRISM implementation, bloodtype.psm *)

(* First we define the domain. We can use strings for naming people.
   However, defining ADT makes the code more robust: spelling errors
   will be caught statically. The original benchmark code (in Balios)
   had a spelling error, which distorted the results.
   We do rely heavily on types here to catch stupid errors.
*)

open Ptypes
open ProbM

type people = Alfred | Anneliese | Annette | Herbert | Kristian 
            | Linus | Marianne | Mette
            | Margot | Nadine | Pauline | Uwe | Willhelm

(* Define father and mother relations *)

let father =
 [(Uwe,Kristian);
  (Uwe,Annette);
  (Willhelm,Uwe);
  (Alfred,Marianne);
  (Kristian,Linus);
  (Kristian,Mette);
  (Herbert,Nadine)]

let mother = 
  [(Marianne,Kristian);
   (Marianne,Annette);
   (Anneliese,Uwe);
   (Pauline,Marianne);
   (Margot,Nadine);
   (Nadine,Linus);
   (Nadine,Mette)];;

(* Compute the inverted relations *)
let father_of = List.map (function (p1,p2) -> (p2,p1)) father
let mother_of = List.map (function (p1,p2) -> (p2,p1)) mother
;;

(* The following is a bit, by 3% at least, faster that List.assq.
   No need to throw exceptions
*)
let rec lookup key = function [] -> None 
  | (h,v)::t -> if h = key then Some v else lookup key t
;;

(* compute founders, who have no ancestors. Verify, that each person
   is either a founder or has both parents. Making this check now
   saves us time checking this fact when doing the inference.
*)
let founders =
  let has_father = List.map (function (_,person) -> person) father in
  let has_mother = List.map (function (_,person) -> person) mother in
  let () = List.iter (fun person -> assert (List.mem person has_mother))
           has_father in
  let () = List.iter (fun person -> assert (List.mem person has_father))
           has_mother in
  List.fold_left (fun s -> function (person,_) ->
      if List.mem person has_father then s else person::s) [] (father @ mother)
;;


type blood_type_gene = GA | GB | GO;;
type blood_type = A | B | O | AB;;

(* Choose a chromosome according to given probabilities *)
let chrom (pa,pb) = dist [(pa,GA); (pb, GB); (1. -. pa -. pb, GO)];;

(* Stochastic functions.
*)

(* Chromosomes of founders. Inferred type: unit -> blood_type_gene *)
let pchromf () = chrom (0.3,0.3)
let mchromf () = chrom (0.3,0.3)
;;

(* Computing the chromosome passed by a father *)
let pchrom = function
  | (GA,GA) -> chrom (0.9,0.05)
  | (GA,GB) -> chrom (0.49,0.49)
  | (GA,GO) -> chrom (0.49,0.02)
  | (GB,GA) -> chrom (0.49,0.49)
  | (GB,GB) -> chrom (0.05,0.9)
  | (GB,GO) -> chrom (0.02,0.49)
  | (GO,GA) -> chrom (0.49,0.02)
  | (GO,GB) -> chrom (0.02,0.49)
  | (GO,GO) -> chrom (0.05,0.05)
;;

(* Computing the chromosome passed by a mother *)
let mchrom = function
  | (GA,GA) -> chrom (0.9,0.05)
  | (GA,GB) -> chrom (0.49,0.49)
  | (GA,GO) -> chrom (0.49,0.02)
  | (GB,GA) -> chrom (0.49,0.49)
  | (GB,GB) -> chrom (0.05,0.9)
  | (GB,GO) -> chrom (0.02,0.49)
  | (GO,GA) -> chrom (0.49,0.02)
  | (GO,GB) -> chrom (0.02,0.49)
  | (GO,GO) -> chrom (0.05,0.05)
;;

(* Choose the bloodtype according to given probabilities *)
let btype (pa,pb,pab) = 
  dist [(pa, A); (pb, B); (pab, AB); (1. -. pa -. pb -. pab, O)];;

(* A stochastic function mapping the genotype, a pair of chromosomes,
   to the phenotype, the blood type
*)
let bloodtype = function
  | (GA,GA) -> btype (0.9,0.03,0.03)
  | (GA,GB) -> btype (0.03,0.03,0.9)
  | (GA,GO) -> btype (0.9,0.04,0.03)
  | (GB,GA) -> btype (0.03,0.03,0.9)
  | (GB,GB) -> btype (0.04,0.9,0.03)
  | (GB,GO) -> btype (0.04,0.9,0.03)
  | (GO,GA) -> btype (0.9,0.04,0.03)
  | (GO,GB) -> btype (0.04,0.9,0.03)
  | (GO,GO) -> btype (0.03,0.03,0.04)
;;


(* Main model *)

(* Guess a chromosome passed from a father and a mother *)
(* Here, we really should use memoization: if we determined the genotype
   of a person, it should be the same on repeated examination.
   However, our genealogical graph has no cycles: there is no incest.
   Since we don't have sharing, we can dispense with memoization.
   See ../noisy-or for an example where memoization is required. *)
let rec pchr person = 
   match lookup person father_of with
   | Some father -> pchrom(pchr father, mchr father)
   | None -> pchromf ()
and mchr person = 
   match lookup person mother_of with
   | Some mother -> mchrom(pchr mother, mchr mother)
   | None -> mchromf ()
;;

(* Inferred type: people -> blood_type *)
let bldtype person = bloodtype(pchr person, mchr person);;

(* Queries: sampling *)

let test1 = sample_importance (random_selector 17) 1000
    (fun () -> bldtype Linus);;

let [(0.207380000000001119, V AB); (0.175530000000001102, V O);
    (0.319309999999997651, V B); (0.297779999999999212, V A)]
 = test1;;

(* Exact result
 In Balios:
 P(bloodtype(linus))=[a:0.32,b:0.31,ab:0.20,null:0.16]
 In Prism:
 P(bloodtype(linus))=[0.32,0.32,0.20,0.16] (exact inference)

*)

(* Conditional inference: P(bloodtype(linus)|pchrom(uwe)=a,mchrom(uwe)=a) *)

(* First, we generalize pchr/mchr to take an additional argument: the
   set of constraints (or, conditions).
   We could have defined this more general procedure from the outset.
   The original pchr/mchr is a particular case when the set of constraints
   is empty.
*)

let rec pchr ((pctx,_) as ctx) person = 
  match lookup person pctx with
  | Some v -> v
  | None -> begin
   match lookup person father_of with
   | Some father -> pchrom(pchr ctx father, mchr ctx father)
   | None -> pchromf ()
  end
and mchr ((_,mctx) as ctx) person = 
  match lookup person mctx with
  | Some v -> v
  | None -> begin
   match lookup person mother_of with
   | Some mother -> mchrom(pchr ctx mother, mchr ctx mother)
   | None -> mchromf ()
 end
;;

(* Conditional probability query *)

let test2 = sample_importance (random_selector 17) 1000 (fun () -> 
  let ctx = [(Uwe,GA)] in
  bloodtype(pchr (ctx,ctx) Linus, mchr (ctx,ctx) Linus));;

(* Obtained result: *)

let [(0.229270000000001473, V AB); (0.113210000000001587, V O);
    (0.220810000000000645, V B); (0.436709999999994658, V A)]
 = test2;;

(*
Other results:

Balios:

P(bloodtype(linus)|pchrom(uwe)=a,mchrom(uwe)=a)=
 [a:0.4391,b:0.2092,ab:0.2354,null:0.1163]
 (approximate values: likelihood sampling with sample size 50000)

Primula:

P(bloodtypeA(linus)|mchromA(uwe),pchromA(uwe))=0.4386
P(bloodtypeB(linus)|mchromA(uwe),pchromA(uwe))=0.2130
P(bloodtypeAB(linus)|mchromA(uwe),pchromA(uwe))=0.2365
P(bloodtype0(linus)|mchromA(uwe),pchromA(uwe))=0.1117
(exact inference; numerical inaccuracies due to rounding in binarization of 
multi-valued predicates)

*)

(* Exact inference *)
(* The functions pchr/mchr as defined above are not suitable for exact
   inference: it takes way too long, more than 10 minutes.
   However, we can do variable elimination, and get the result within
   a second.
   We use the most general pchr/mchr.
*)

let rec pchr ((pctx,_) as ctx) person = 
  match lookup person pctx with
  | Some v -> v
  | None -> begin
   match lookup person father_of with
   | Some father -> pchrom(variable_elim (pchr ctx) father, 
			   variable_elim (mchr ctx) father)
   | None -> pchromf ()
  end
and mchr ((_,mctx) as ctx) person = 
  match lookup person mctx with
  | Some v -> v
  | None -> begin
   match lookup person mother_of with
   | Some mother -> mchrom(variable_elim (pchr ctx) mother, 
			   variable_elim (mchr ctx) mother)
   | None -> mchromf ()
 end
;;

(* Unconditional predicate: with the empty constraints *)
let bldtype person = bloodtype(pchr ([],[]) person, mchr ([],[]) person);;

(* Unconditional query *)
let test1exact = exact_reify (fun () -> bldtype Linus);;

let [(0.197860551516677169, V AB); (0.159477710751046636, V O);
     (0.320852692775250137, V B); (0.32180904495702678, V A)]
    = test1exact;;

(* Query for the conditional probability *)
let test2exact = exact_reify (fun () -> 
  let ctx = [(Uwe,GA)] in
  bloodtype(pchr (ctx,ctx) Linus, mchr (ctx,ctx) Linus));;

(* The following is result is obtained nearly instantaneously.
   It perfectly matches the exact result of Primula. 
   It seems Balios cannot do exact inference for the conditional
   probability query. The benchmark code does not include any conditional
   probability queries in PRISM. I wonder why.
*)
let [(0.236503769769331712, V AB); (0.111720805234742399, V O);
   (0.213085457329678429, V B); (0.438689967666247682, V A)]
    = test2exact;;

