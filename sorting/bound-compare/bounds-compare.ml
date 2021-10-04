(* OCaml program to:

   (1) generate and print out the two lower-approximations to the
   target sorting lower bound, plus the target itself, for a range of
   values of len

   (2) compare int_log_up 2 (fact len) (our greatest lower bound) and
   wc len (our smallest upper bound), for a range of values of len *)

open Batteries
open Big_int  (* arbitrary precision integers *)
open Printf

(* exponentiation *)

let pow (b : int) (n : int) : int =
  let rec pw (r : int) (n : int) : int =
    if n = 0
    then r
    else pw (Int.( * ) r b) (Int.(-) n 1) in
  pw 1 n

(* <= for big_int *)

let le (n : big_int) (m : big_int) : bool =
  match compare n m with
  | -1 -> true
  | 0  -> true
  | _  -> false

(* < for big_int *)

let lt (n : big_int) (m : big_int) : bool =
  match compare n m with
  | -1 -> true
  | _  -> false

let (two : big_int) = of_int 2

(* factorial *)

let rec fact (n : int) : big_int =
  if n = 0 then one else of_int n * fact (Int.(-) n 1)

(* il is int_log 2 *)

let rec il_find (n : big_int) (i : int) (p : big_int) : int =
  if le p n && lt n (p * two)  (* p is two to the power i *)
  then i
  else il_find n (Int.(+) i 1) (p * two)

let il (n : big_int) : int =
  if le n zero
  then raise (Failure "arg must be at least 1")
  else il_find n 0 one

(* ilu is int_log_up 2 *)

let rec ilu_find (n : big_int) (i : int) (p : big_int) : int =
  if lt p n && le n (p * two)  (* p is two to the power i *)
  then Int.(+) i 1
  else ilu_find n (Int.(+) i 1) (p * two)

let ilu (n : big_int) : int =
  if le n zero
    then raise (Failure "arg must be at least 1")
  else if equal n one
    then 0
  else ilu_find n 0 one

(* integer division, rounding up *)

let divup (n : int) (m : int) : int =
  Int.(+) (Int.(/) n m) (if n mod m = 0 then 0 else 1)

(* upper bound on worst case of number of comparisons
   needed when sorting a list of distinct elements of
   length n *)

let rec wc (n : int) : int =
  if n <= 1
  then 0
  else Int.(+)
       (wc (Int.(/) n 2))
       (Int.(+)
        (wc (divup n 2))
        (Int.(-) n 1))

(* return the two lower-approximations plus the target;
   mathematically:

   n * int_log n %/ 2,
   n * int_log n - 2 * 2 ^ int_log 2 n,
   int_log_up 2 (fact n) *)

let low_approxs (n : int) : int * int * int =
  let il_n = il (of_int n) in
  ((Int.(/) (Int.( * ) n il_n)) 2,
   Int.(-) (Int.( * ) n il_n) ((Int.( * ) 2 (pow 2 il_n))),
   ilu (fact n))

(* run low_approxs on a range, from 1 to n, collecting the results *)

let rec range_low_approxs (n : int) : (int * (int * int * int)) list =
  if n = 0
  then []
  else range_low_approxs (Int.(-) n 1) @ [(n, low_approxs n)]

(* print a result of low_approxs *)

let pr_low_approxs ((n, (i, j, k)) : int * (int * int * int)) : unit =
  printf "%3d:   %5d    %5d    %5d\n" n i j k

(* run low_approxs on a range, from 1 to n, and print the results *)

let run_low_approxs (n : int) : unit =
  List.iter pr_low_approxs (range_low_approxs n)

(* return int_log_up 2 (fact n) paired with wc n *)

let low_upp (n : int) : int * int =
  (ilu (fact n), wc n)

(* run low_upp on a range, from 1 to n, collecting the results *)

let rec range_low_upp (n : int) : (int * (int * int)) list =
  if n = 0
  then []
  else range_low_upp (Int.(-) n 1) @ [(n, low_upp n)]

(* print a result of low_upp *)

let pr_low_upp ((n, (i, j)) : int * (int * int)) : unit =
  printf "%3d:   %5d    %5d\n" n i j

(* run low_upp on a range, from 1 to n, and print the results *)

let run_low_upp (n : int) : unit =
  List.iter pr_low_upp (range_low_upp n)
