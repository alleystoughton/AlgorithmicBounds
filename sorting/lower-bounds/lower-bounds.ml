(* OCaml program to generate and print out the two
   lower-approximations to the target sorting lower bound, plus the
   target itself, for a range of values of len *)

open Batteries
open Big_int
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
  if n = 0 then one else (of_int n) * (fact (Int.(-) n 1))

(* il is int_log 2 *)

let rec il_find (n : big_int) (i : int) (p : big_int) : int =
  if le p n && lt n (p * two)
  then i
  else il_find n (Int.(+) i 1) (p * two)

let il (n : big_int) : int =
  if le n zero
  then raise (Failure "arg must be at least 1")
  else il_find n 0 one

(* ilu is int_log_up 2 *)

let rec ilu_find (n : big_int) (i : int) (p : big_int) : int =
  if lt p n && le n (p * two)
  then Int.(+) i 1
  else ilu_find n (Int.(+) i 1) (p * two)

let ilu (n : big_int) : int =
  if le n zero
    then raise (Failure "arg must be at least 1")
  else if equal n one
    then 0
  else ilu_find n 0 one

(* return the two lower-approximations plus the target *)

let f (n : int) : int * int * int =
  let il_n = il (of_int n) in
  ((Int.(/) (Int.( * ) n il_n)) 2,
   Int.(-) (Int.( * ) n il_n) ((Int.( * ) 2 (pow 2 il_n))),
   ilu (fact n))

(* fun f on a range, collecting the results *)

let rec g (n : int) : (int * (int * int * int)) list =
  if n = 0
  then []
  else g (Int.(-) n 1) @ [(n, f n)]

(* print a result *)

let pr ((n, (i, j, k)) : int * (int * int * int)) : unit =
  printf "%3d:   %5d    %5d    %5d\n" n i j k

(* run g on a range and print the results *)

let run (n : int) : unit =
  List.iter pr (g n)
