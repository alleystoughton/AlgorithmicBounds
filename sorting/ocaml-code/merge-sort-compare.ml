(* OCaml program to compare, for a given list length, len:

   - the worst case number of comparisons used by merge sort;

   - wc len;

   - len * int_log 2 len *)

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

(* assuming perm is a permutation on 0 .. length perm - 1, the
   elements of xs and ys are in the range 0 .. length perm - 1, and xs
   and ys are sorted according to cmp_of_perm perm, merge xs and ys so
   the result is sorted according to cmp_of_perm perm; for each
   comparison carried out, increment the contents of cr *)

let rec merge
      (perm : int list) (cr : int ref) (xs : int list) (ys : int list)
        : int list =
  match xs with
  | []      -> ys
  | x :: xs ->
      match ys with
      | []      -> x :: xs
      | y :: ys ->
         (cr := !cr + 1;
          if cmp_of_perm perm x y
          then x :: merge perm cr xs (y :: ys)
          else y :: merge perm cr (x :: xs) ys)

(* assuming perm is a permutation on 0 .. length perm - 1, sort xs
   according to cmp_of_perm perm; for each comparison carried out,
   increment the contents of cr *)

let rec merge_sort (perm : int list) (cr : int ref) (xs : int list) =
  match xs with
  | [x] -> [x]
  | xs ->
     let mid = List.length xs / 2 in
     let ys = List.take mid xs in
     let zs = List.drop mid xs in
     merge perm cr (merge_sort perm cr ys) (merge_sort perm cr zs)

(* given a permutation on 0 .. length perm - 1, use merge_sort
   to sort (upto (length perm)) according to cmp_of_perm perm,
   returning only the number of comparisons carried out *)

let run_merge_sort_on_upto (perm : 'a list) : int =
  let cr = ref 0 in
  let _ = merge_sort perm cr (upto (length perm)) in
  !cr

(* exponentiation *)

let rec pow (n : int) (m : int) : int =
  if m = 0
  then 1
  else n * pow n (m - 1)

(* auxiliary function for int_log 2 *)

let rec il_find (n : int) (i : int) : int =
  if pow 2 i <= n && n < pow 2 (i + 1)
  then i
  else il_find n (i + 1)

(* int_log 2 *)

let il (n : int) : int =
  if n <= 0
  then raise (Failure "arg must be at least 1")
  else il_find n 0

(* integer division, rounding up *)

let divup (n : int) (m : int) : int =
  n / m + (if n mod m = 0 then 0 else 1)

(* upper bound on worst case number of comparisons carried out by
   merge sort when sorting a list of length n whose elements are in
   the range 0 .. n - 1 according to the comparison function
   corresponding to a permutation of upto n *)

let rec wc (n : int) : int =
  if n <= 1
  then 0
  else wc (n / 2) + wc (divup n 2) + n - 1

(* collect

   - maximum over all permutations, perm, on 0 .. len - 1 of the
   number of comparisons carried out when sorting upto n according to
   the comparison function of perm;

   - wc len;

   - len * int_log 2 len *)

let compare (len : int) : int * (int * int * int) =
  (len,
   (max (map run_merge_sort_on_upto (all_perms (upto len))),
    wc len,
    len * il len))

(* print a result of compare *)

let pr_compare ((len, (i, j, k)) : int * (int * int * int)) : unit =
  Printf.printf "%2d:   %2d   %2d   %2d\n" len i j k

(* run compare on all the numbers between 1 and n *)

let rec compare_range (n : int) : (int * (int * int * int)) list =
  if n = 0
  then []
  else compare_range (n - 1) @ [compare n]

(* run compare on all the numbers between 1 and n, printing
   the results *)

let run_compare_range (n : int) : unit =
  List.iter pr_compare (compare_range n)
