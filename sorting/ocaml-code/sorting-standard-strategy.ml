(* OCaml program for simulating lower bound game executions for our
   adversary and over all query sequences, returning the minimum final
   stage numbers *)

open Batteries
open List

(* return the list consisting of 0 .. n - 1 *)

let rec upto (n : int) : int list =
  match n with
  | 0 -> []
  | n -> upto (n - 1) @ [n - 1]

(* return all the lists formed by inserting x into ys in some position
   *)

let rec all_insert (x : 'a) (ys : 'a list) : 'a list list =
  match ys with
  | []      -> [[x]]
  | y :: ys ->
      [x :: y :: ys] @
      map (fun zs -> y :: zs) (all_insert x ys)

(* return all the permutations of xs *)

let rec all_perms (xs : 'a list) : 'a list list =
  match xs with
  | []      -> [[]]
  | x :: xs ->
      concat (map (all_insert x) (all_perms xs))

(* turn a permutation on 0 .. length perm - 1 into a comparison
   function on elements of this range *)

let cmp_of_perm (perm : 'a list) (x : int) (y : int) : bool =
  match index_of x perm with
  | None   -> raise (Failure "should not happen")
  | Some i ->
      match index_of y perm with
      | None   -> raise (Failure "should not happen")
      | Some j -> i <= j

(* generate all queries of the form (i, j) where 0 <= i < j < len;
   this is a restriction over what the lower bound game allows,
   but we conjecture it doesn't affect the results *)

let queries len =
  let xs = upto len in
  filter
  (fun q -> (fst q) < (snd q))
  (cartesian_product xs xs)

(* generate lower bound game executions continuing from the given
   stage, inpss and queries, returning the minimum final stage *)

let rec search
      (stage : int) (inpss : int list list) (queries : (int * int) list)
        : int =
  if length inpss <= 1
    then stage
  else if queries = []
    then raise (Failure "this should not happen")
  else min
       (map
        (fun (q : int * int) ->
           let (inpss_q_true, inpss_q_false) =
             partition
             (fun inps -> cmp_of_perm inps (fst q) (snd q))
             inpss in
           if length inpss_q_true <= length inpss_q_false
           then search (stage + 1) inpss_q_false (remove queries q)
           else search (stage + 1) inpss_q_true (remove queries q))
        queries)

(* work through all lower bound game executions for our adversary, and
   for all query sequences (restricted to queries of the form (i, j)
   where 0 <= i < j < len), returning the minimum final stage
   number *)

let minimum_stage_of_game_run (len : int) : int =
  search 0 (all_perms (upto len)) (queries len)
