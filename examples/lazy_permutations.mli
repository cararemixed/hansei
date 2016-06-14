(* Correlated memoization: building stochastic injective functions,
   or sampling permutations lazily.
*)


(* Uniformly select an element from a list *)
val uniformly_list : 'a list -> 'a


(* Uniformly select one element from a list and return it and the remainder *)
val uniformly_uncons : 'a list -> 'a * 'a list

(* Return a permutation of a list. Each element in the result must be
   forced first
*)
val lazy_permutation : 'a list -> (unit -> 'a) list


(* A different version, based on insertion rather than
   selection sort.
   It computes the sequence of N all-different random variables
   with the range [0..N-1].
   A sample from a sequence has no duplicates, and is
   a permutation from [0..N-1]
*)

val lazy_permutation_ins : int -> (unit -> int) list


(* Auxiliary deterministic functions *)

(* Split a list at the given element n and return the zipper:
   the first (n-1) elements, in the inverse order, and the tail of the list.
   The n-th element is at the head of the tail.
   If the given list has fewer than n elements, the tail will be empty.
*)
val split_at : int -> 'a list -> 'a list * 'a list

