(* Parser combinators with Hansei *)

(*
These are parser combinators over a non-deterministic stream.
They can emulate not only parsing of a stream (that is, parsing
forwards) but also determining a stream for the given parse
(parsing backwards).

The current file is inspired by and is meant to reprodue the examples
from Curry:

http://www.informatik.uni-kiel.de/~curry/examples/parsing/palindrome.curry
http://www.informatik.uni-kiel.de/~curry/examples/parsing/expr_parser.curry

*)

open ProbM;;				(* Import HANSEI *)

(*
#load "prob.cma";;
*)
let letlazy = ProbM.letlazy_nesting;;	(* for the sake of 'many' *)

(* The type of a stream *)
type stream_v = Eof | Cons of char * stream
and stream = unit -> stream_v
;;

(* Convert between a stream and a character string *)
let stream_of_string : string -> stream = fun sg ->
  let rec loop i =
    if i >= String.length sg then Eof else
    Cons (sg.[i], fun () -> loop (succ i))
  in fun () -> loop 0
;;

(* This is a deterministic (!) function, with an embedded
   state effect.
   One should never use mix state effect with non-determinism!
*)
let string_of_list : char list -> string = fun lst ->
  let b = Buffer.create 17 in
  let rec loop = function
    | []       -> Buffer.contents b
    | (h::t)   -> Buffer.add_char b h; loop t
  in loop lst
;;

(* This is a non-deterministic function. It should not use any state
   effect when non-determinism may be present.
*)
let string_of_stream : stream -> string = 
  let rec loop acc = function
    | Eof        -> string_of_list (List.rev acc)
    | Cons (c,t) -> loop (c::acc) (t ())
  in fun st -> loop [] (st ())
;;
 
(* Generate a random stream over a given alphabet *)

let stream_over : char array -> stream = fun ca ->
  let rec loop () =
    if flip 0.5 then Cons (uniformly ca, letlazy loop)
                else Eof
  in letlazy loop
;;

  

(* Parsers with the result (of its `semantic action') of 'a *)
type 'a parser = stream -> 'a * stream
;;

(* Primitive parsers *)

(* A parser for the end of input *)
let eof : unit parser = fun st ->
  match st () with
  | Eof -> ((),st)
  | _   -> fail ()
;;

(* Injection: a parser that parses epsilon and produces a given value *)
let pure : 'a -> 'a parser = fun x st -> (x,st);;

(* A recognizer for an empty string *)
let empty : unit parser = pure ();;

(* A parser that checks if the current stream element satisfies the given
   predicate
*)

let p_sat : (char -> bool) -> char parser = fun pred st ->
  match st () with
  | Cons (c,st) when pred c -> (c,st)
  | _                       -> fail ()
;;

(* A parser for a single character *)
let p_char : char -> char parser = fun c -> p_sat (fun x -> x = c);;


(* Parser combinators *)

(* Alternation *)
let (<|>) : 'a parser -> 'a parser -> 'a parser = fun p1 p2 st ->
  uniformly [|p1;p2|] st
;;

(* Multi-way, uniform alternation *)
let alt : 'a parser array -> 'a parser = fun pa st ->
  uniformly pa st
;;

(* Applicative *)
let (<*>) : ('a -> 'b) parser -> 'a parser -> 'b parser = fun p1 p2 st ->
  let (f,st) = p1 st in
  let (v,st) = p2 st in
  (f v,st)
;;

(* A particular case: fmap f = pure f <*> *)
let (<$>) : ('a -> 'b) -> 'a parser -> 'b parser = fun f p st ->
  let (v,st) = p st in (f v, st)
;;

(* Another particular case: disregard the value of one of the parsers,
   left or right 
*)
let ( *> ) : 'a parser -> 'b parser -> 'b parser = fun p1 p2 st ->
  let (_,st) = p1 st 
  in p2 st
;;

let ( <* ) : 'a parser -> 'b parser -> 'a parser = fun p1 p2 st ->
  let (v,st) = p1 st in
  let (_,st) = p2 st in
  (v,st)
;;

(* Fix-point *)
let p_fix : ('a parser -> 'a parser) -> 'a parser = fun f ->
  let rec p st = f p st in p
;;

(*
(* Repetion, without the maximal-munch property *)
let rec many : 'a parser -> 'a list parser = fun p st ->
  (pure [] <|> ((fun x xs -> x :: xs) <$> p <*> many p))
  st
;;
*)

(* Repetion, with the maximal munch property *)

let soft_cut : (unit -> 'a) -> ('a -> 'w) -> (unit -> 'w) -> 'w =
  fun p q r ->
    match Inference.first_success (reify0 p) with
    | [] -> r ()
    | t  -> q (reflect t)
;;

let many : 'a parser -> 'a list parser = fun p ->
  let rec self st =
    soft_cut (fun () -> p st)		(* check parser's success  *)
             (fun (v,st) -> 		(* continue parsing with p *)
	       let (vs,st) = self st in
	       (v::vs,st))
             (fun () -> ([],st))	(* total failure of the parser *)
  in self
;;


(* A repetition with at least one occurrence *)
let many1 : 'a parser -> 'a list parser = fun p ->
  (fun x xs -> x::xs) <$> p <*> many p
;;

(* Run the parser `forward': completely parse the given string *)
let run_fwd : 'a parser -> string -> 'a Ptypes.pV = fun p s ->
  exact_reify (fun () ->
    let (v,s) = p (stream_of_string s) in
    if s () <> Eof then fail (); v)
;;



(* Implementing the palindrome example from Curry:
   A parser for palindromes over the alphabet 'a' and 'b'
   http://www.informatik.uni-kiel.de/~curry/examples/parsing/palindrome.curry

Curry code:

a = terminal 'a'
b = terminal 'b'

pali = empty <|> a <|> b <|> a<*>pali<*>a <|> b<*>pali<*>b

*)

(* This is a recognizer: semantic actions all return unit *)
let pali = p_fix (fun pali ->
  empty <|> ((fun _ -> ()) <$> p_char 'a')
        <|> ((fun _ -> ()) <$> p_char 'b')
        <|> (p_char 'a' *> pali <* p_char 'a')
        <|> (p_char 'b' *> pali <* p_char 'b')
    )
;;

(* Examples *)

(* Forward parsing: recognizing palindromes *)
let [] = run_fwd pali "ab";;

let [(0.015625, Ptypes.V ())] = 
  run_fwd pali "aa";;

let [(0.00390625, Ptypes.V ())] =
  run_fwd pali "aaaa";;

let [(0.03125, Ptypes.V ())] =
  run_fwd pali "aba";;

let [(0.001953125, Ptypes.V ())] =
  run_fwd pali "abaaba";;

(* Re-define with the uniform alternation *)
(* The order of the alternatives is immaterial. *)
let pali = p_fix (fun pali ->
  alt [| empty;
	 (fun _ -> ()) <$> p_char 'a';
         (fun _ -> ()) <$> p_char 'b';
         p_char 'a' *> pali <* p_char 'a';
         p_char 'b' *> pali <* p_char 'b' |]
    )
;;

let [] = 
  run_fwd pali "ab";;

let [(0.0399999999999999939, Ptypes.V ())] =
  run_fwd pali "aa";;

let [(0.008, Ptypes.V ())] =
  run_fwd pali "aaaa";;

let [(0.0400000000000000078, Ptypes.V ())] =
  run_fwd pali "aba";;

let [(0.0016, Ptypes.V ())] =
  run_fwd pali "abaaba";;

(* Backwards parsing: generating palndromes *)
(* The first argument to run_bwd is the search depth limit; unlimited
   if None. 
*)
let run_bwd : 
  int option -> 'a parser -> (unit -> stream) -> ('a * string) Ptypes.pV 
    = fun n p stm ->
      Inference.explore n (reify0 (fun () ->
	let st = stm () in
	let (v,st') = p st in
	if st' () <> Eof then fail (); 
        (v,string_of_stream st)))
;;

(* Let's see first what stream_over does.  
   We cannot use exact_reify since the search tree is infinite.
   We have to limit the depth of the search, say, to 5 levels.
   Here is what we get.
*)
Inference.explore (Some 5) (reify0 (fun () ->
   string_of_stream (stream_over [|'a';'b'|]) ));;

(* Generating some palindromes, for the search depth 10 *)
run_bwd (Some 10) pali (fun () -> stream_over [|'a';'b'|]);;

(* Make sure the stream has exactly n elements *)
let rec stream_len st n = match (st (),n) with
  | (Eof,0)                   -> ()
  | (Cons (_,t),n) when n > 0 -> stream_len t (n-1)
  | _                         -> fail ()
;;

(* Make sure the stream has exactly at most n elements *)
let rec stream_at_most_len st n = match (st (),n) with
  | (Eof,_)                   -> ()
  | (Cons (_,t),n) when n > 0 -> stream_at_most_len t (n-1)
  | _                         -> fail ()
;;

(* Generating all palindromes of length 5 *)
(* The generation is exhaustive *)

run_bwd None pali (fun () ->
  let st = stream_over [|'a';'b'|] in
  stream_len st 5; st)
;;

(* They are generated with uniform probabilities... *)
(*
[(3.90625000000000093e-06, Ptypes.V ((), "bbbbb"));
 (3.90625000000000093e-06, Ptypes.V ((), "bbabb"));
 (3.90625000000000093e-06, Ptypes.V ((), "babab"));
 (3.90625000000000093e-06, Ptypes.V ((), "baaab"));
 (3.90625000000000093e-06, Ptypes.V ((), "abbba"));
 (3.90625000000000093e-06, Ptypes.V ((), "ababa"));
 (3.90625000000000093e-06, Ptypes.V ((), "aabaa"));
 (3.90625000000000093e-06, Ptypes.V ((), "aaaaa"))]
*)

(* The Curry code: *)
(* pali5 = findall (\[x1,x2,x3,x4,x5] -> pali [x1,x2,x3,x4,x5] =:= []) *)


(* A few tests of 'many', making sure it really follows the maximal munch
   principle
*)


let [(1., Ptypes.V [])] = run_fwd (many (p_char 'a') <* p_char 'b') "b";;

let [(1., Ptypes.V ['a'; 'a'; 'a'])] =
   run_fwd (many (p_char 'a') ) "aaa";;

(* Only one answer! No ambiguity *)
let [(1., Ptypes.V (['a'; 'a'; 'a'], []))] =
   run_fwd ((fun x y -> (x,y)) <$> 
            many (p_char 'a') <*> many (p_char 'a')) "aaa";;

(* No match *)
let [] = run_fwd (many (p_char 'a') <* p_char 'a') "aaa";;


let [(0.03125, Ptypes.V ['a'; 'b'; 'a'; 'b'; 'b'])] =
  run_fwd (many ((p_char 'a') <|> (p_char 'b'))) "ababb";;


let [(1., Ptypes.V [['a'; 'a'; 'a']])] =
  run_fwd (many (many1 (p_char 'a'))) "aaa";;

(* Again, only a single answer! *)
let [(0.0625, Ptypes.V [['a'; 'a'; 'a']; ['b']; ['a']; ['b']])] =
  run_fwd (many ((many1 (p_char 'a')) <|> (many1 (p_char 'b'))))
    "aaabab";;

let [(0.25, Ptypes.V ["aa"; "a"]); (0.25, Ptypes.V ["a"; "aa"]);
     (0.125, Ptypes.V ["a"; "a"; "a"])] =
run_fwd ((many ((pure "aa" <* p_char 'a' <* p_char 'a') <|>
               (pure "a" <* p_char 'a'))) <* p_char 'b') "aaab";;

(* Previously
run_fwd ((fun x y -> (x,y))  <$>
	   (many ((pure "aa" <* p_char 'a' <* p_char 'a') <|>
               (pure "a" <* p_char 'a')))
	   <*> p_char 'a') "aaa";;

      - : (string list * char) Ptypes.pV =
[(0.25, Ptypes.V (["aa"], 'a')); (0.125, Ptypes.V (["a"; "a"], 'a'))]

And here this is just wrong: we should've failed since we can munch all a's. 
*)

(* A tricky example that shows it is NOT the case that
   many (p1 | p2) >= many p1 | many p2
 where >= is to be understood as language inclusion.
 This inequality does hold for many without maximum munch.
*)
let [] =
run_fwd ((many ((p_char 'a' <* p_char 'a') <|> p_char 'a'))
	   <* p_char 'a') "aaa";;

(* However, it should still hold that
   (many p) (st1 | st2) = many p st1 | many p st2
*)

let
[(0.0078125, Ptypes.V ((['a'; 'a'], 'b'), "aab"));
 (0.03125, Ptypes.V ((['a'], 'b'), "ab"));
 (0.125, Ptypes.V (([], 'b'), "b"))]
=
run_bwd None ((fun x y -> (x,y))  <$>
    many (p_char 'a') <*> p_char 'b') 
   (fun () -> let st = stream_over [|'a';'b'|] in
              stream_at_most_len st 3; st);;

(* generation of the language a* *)

let [(0.0078125, Ptypes.V (['a'; 'a'; 'a'], "aaa"));
     (0.03125, Ptypes.V (['a'; 'a'], "aa")); 
     (0.125, Ptypes.V (['a'], "a"));
     (0.5, Ptypes.V ([], "")); 
     (0.00390625, Ptypes.C _);
     (0.00390625, Ptypes.C _)] =
run_bwd (Some 9) (many (p_char 'a')) (fun () -> stream_over [|'a';'b'|]);;

(*
A simple expression parser for arithmetic expressions over natural numbers
The parser returns the expression result.

http://www.informatik.uni-kiel.de/~curry/examples/parsing/expr_parser.curry

Here is the parser in Curry:

expression   =  term t <*> plus_minus op <*> expression e  >>> (op t e)
           <||> term
 where op,t,e free

term         =  factor f <*> prod_div op <*> term t        >>> (op f t)
           <||> factor
 where op,f,t free

factor       =  terminal '(' <*> expression e <*> terminal ')'  >>> e
           <||> num
 where e free

plus_minus   =  terminal '+'  >>> (+)
           <||> terminal '-'  >>> (-)

prod_div     =  terminal '*'  >>> (*)
           <||> terminal '/'  >>> div

num = some digit l >>> numeric_value l
  where l free
        numeric_value ds = foldl1 ((+) . (10*)) (map (\c->ord c - ord '0') ds)

digit = satisfy isDigit
*)

let digit = (fun c -> Char.code c - Char.code '0') <$>
            p_sat (fun x -> x >= '0' && x <= '9');;

let num = (List.fold_left (fun acc d -> d + acc * 10) 0) <$> many1 digit ;;

let [(1., Ptypes.V 123)] = run_fwd num "123";;


let plus_minus = ((fun _ -> (+)) <$> p_char '+') <|>
                 ((fun _ -> (-)) <$> p_char '-')
;;

let prod_div = ((fun _ -> ( * )) <$> p_char '*') <|>
               ((fun _ -> ( / )) <$> p_char '/')
;;

(* The grammar is not factored -- just as the Curry grammar wasn't *)
let rec expression st =
  ( ((fun t1 op t2 -> op t1 t2) <$> term <*> plus_minus <*> expression) <|>
    term
  ) st
and term st =
  ( ((fun t1 op t2 -> op t1 t2) <$> factor <*> prod_div <*> term) <|>
    factor
  ) st
and factor st =
  ( (p_char '(' *> expression <* p_char ')') <|>
    num
  ) st
;;

let [(0.125, Ptypes.V 10)] =
  run_fwd expression "10";;


let [(1.52587890625e-05, Ptypes.V 5)] =
  run_fwd expression "(10+5*2)/4";;

(* Curry: expression val "(10+5*2)/4" =:= [] where val free *)

(* Generating some expressions *)

let exp_stream () =
  let st = stream_over [|'0';'1';'2';'3';'4';'5';'6';'7';'8';'9';
			 '+';'-';'*';'(';')'|]
  in stream_len st 4; st
;;

(* Show only values, don't show continuations *)
let rec only_val = function 
  | [] -> []
  | (((_,Ptypes.V _) as i) :: t) -> i :: only_val t
  | (_::t) -> only_val t
;;


(* let ((3.08641975308642e-07, Ptypes.V (9999, "9999")):: *)
(*      (3.08641975308642e-07, Ptypes.V (9998, "9998")):: *)
(*      _)					(\* and many more *\) *)
(* =  *)
(* only_val (run_bwd (Some 14) factor exp_stream);; *)

let
[(0.000390624999999999967, Ptypes.V (7139, "7139"));
 (0.000390624999999999967, Ptypes.V (5164, "5164"))]
 =
sample_importance (random_selector 17) 80
(fun () ->
	let st = exp_stream () in
	let (v,st') = expression st in
	if st' () <> Eof then fail (); 
        (v,string_of_stream st))
;;

let [(2.60416666666666626e-07, Ptypes.V (5, "05*1"))] =
sample_importance (random_selector 37) 30000
(fun () ->
	let st = exp_stream () in
	let (v,st') = expression st in
	if st' () <> Eof then fail (); 
        if v <> 5 then fail ();
        (v,string_of_stream st))
;;

(* more balanced  stream *)
let exp_stream () =
  let ch () =
   if flip 0.7 then uniformly [|'+';'-';'*';'(';')'|]
   else uniformly [|'0';'1';'2';'3';'4';'5';'6';'7';'8';'9'|] in
  letlazy (fun () -> Cons (ch (), 
  letlazy (fun () -> Cons (ch (), 
  letlazy (fun () -> Cons (ch (), 
  letlazy (fun () -> Cons (ch (), fun () -> Eof))))))))
;;

let ((4.05000000000000305e-07, Ptypes.V (9999, "9999"))::
     (4.05000000000000305e-07, Ptypes.V (9998, "9998"))::
     _)					(* and many more *)
 =
only_val (run_bwd (Some 14) factor exp_stream);;

let [(0.0005, Ptypes.V (3403, "3403")); (0.0005, Ptypes.V (1396, "1396"));
 (2.0000000000000005e-05, Ptypes.V (92, "(92)"));
 (2.0000000000000005e-05, Ptypes.V (66, "(66)"));
 (2.5e-05, Ptypes.V (64, "55+9")); (2.5e-05, Ptypes.V (63, "55+8"));
 (2.5e-05, Ptypes.V (62, "55+7")); (2.5e-05, Ptypes.V (61, "55+6"));
 (2.5e-05, Ptypes.V (60, "55+5")); (2.5e-05, Ptypes.V (59, "55+4"));
 (2.5e-05, Ptypes.V (58, "55+3")); (2.5e-05, Ptypes.V (57, "55+2"));
 (2.5e-05, Ptypes.V (56, "55+1"));
 (2.50000000000000215e-05, Ptypes.V (55, "55+0"))] =
sample_importance (random_selector 17) 2000
(fun () ->
	let st = exp_stream () in
	let (v,st') = expression st in
	if st' () <> Eof then fail (); 
        (v,string_of_stream st))
;;

(* Find expressions whose value is 5 *)
let [(1.66666666666666666e-06, Ptypes.V (5, "03+2"))] =
sample_importance (random_selector 17) 30000
(fun () ->
	let st = exp_stream () in
	let (v,st') = expression st in
	if st' () <> Eof then fail (); 
        if v <> 5 then fail ();
        (v,string_of_stream st))
;;


print_endline "\nAll Done\n";;

