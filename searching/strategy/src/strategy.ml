(* Searching for Optimal Adversarial Strategies for Searching Problem *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2021 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* find optimal adversarial strategies for searching for the first
   occurrence of a given element in a sorted list of a given arity,
   where the list is guaranteed to have at least one occurrence of the
   element; the algorithm's goal is to find the index of that first
   occurrence

   the command line arguments allow users to specify:

   (+) the size, univ-size, of the prefix of the lowercase letters
       'a', ..., 'z' that is the universe of elements;

   (+) the arity of the lists of elements of the universe that are
       being searched;

   (+) the element being searched for

   the option -minimum-path-length says to only print out the minimum
   path length of the optimal strategy *)

open Batteries
open List
open Printf
open Arg

type inp = char

let lowers = List.of_enum (Char.(--) 'a' 'z')

let string_to_inp_opt (s : string) : char option =
  if String.length s = 1 &&
     'a' <= s.[0] && s.[0] <= 'z'
  then Some s.[0]
  else None

(* test whether a list of inp's is sorted in (not necessarily
   strictly) ascending order *)

let rec sorted (xs : inp list) : bool =
  match xs with
  | []           -> true
  | [_]          -> true
  | x :: y :: zs -> x <= y && sorted (y :: zs)

(* prod xss yss returns all lists that can be formed by
   appending an element of xss to an element of yss *)

let prod (xss : 'a list list) (yss : 'a list list) : 'a list list =
  map (uncurry append) (cartesian_product xss yss)

(* when n >= 0, pow xs n returns all lists that can be formed by
   appending n elements (some possibly occurring multiple times) of
   xs *)

let rec pow (xs : 'a list) (n : int) : 'a list list =
  if n = 0
  then [[]]
  else prod (map singleton xs) (pow xs (n - 1))

(* a list of elements (of length arity over the universe) is good,
   relative to x, iff it is sorted and has at least one occurrence of
   x *)

let good (x : inp) (inps : inp list) : bool =
  sorted inps && mem x inps

(* if arity >= 1, then init_inpss x arity is all the `good x` lists of
   elements of univ of length arity *)

let init_inpss (univ : inp list) (x : inp) (arity : int) =
  filter (good x) (pow univ arity)

(* assuming all elements of inpss have length arity and 0 <= i <
   arity, then keep just those inps in inpss that have a at position i
   *)

let filter_nth (inpss : inp list list) (i : int) (a : inp)
      : inp list list =
  filter
  (fun (inps : inp list) -> nth inps i = a)
  inpss

(* assuming inps has at least one occurrence of x, f x inps
   returns the least index of such an occurrence *)

let f (x : inp) (inps : inp list) : int =
  let rec h i ys =
    match ys with
    | []      -> raise (Failure "didn't have distinguished element")
    | y :: ys -> if y = x then i else h (i + 1) ys in
  h 0 inps

(* tests whether all elements of xs are the same (true when xs is
   empty) *)

let all_same (xs : 'a list) : bool =
  match xs with
  | []      -> true
  | x :: xs -> for_all ((=) x) xs

let inpss_done (x : inp) (inpss : inp list list) : bool =
  all_same (map (f x) inpss)

(* adversarial strategy *)

type strategy =
  | Done                (* no queries remain *)
  | Next of (int *      (* algorithm's query *)
             inp *      (* adversary's answer *)
             strategy)  (* strategy for rest of game *)
            list        (* should be ordered by first component *)

let strategy_of ((_, _, strat) : int * inp * strategy) = strat

let rec min_path_length (strat : strategy) : int =
  match strat with
  | Done       -> 0
  | Next nexts ->
      1 + min (map (fun t -> min_path_length (strategy_of t)) nexts)

(* assuming xs is nonempty, returns the element of xs with largest
   metric, favoring earlier elements in the list *)

let rec optimal (metric : 'a -> int) (xs : 'a list) : 'a =
  match xs with
  | []      -> raise (Failure "cannot be empty")
  | [x]     -> x
  | x :: xs ->
      let y = optimal metric xs in
      if metric x >= metric y then x else y

(* if n >= 0, then upto n returns [0; 1; ...; n - 1] *)

let upto (n : int) : int list =
  let rec up i =
    if i = n then [] else i :: up (i + 1) in
  up 0

(* opt_strat_from takes in the universe, univ, the element x of univ
   to be searched for, the list qs of queries that haven't yet been
   asked, the result of filtering `init_inpss univ x arity` by the
   queries (the result of removing the members of qs from upto arity)
   already asked by the algorithm and the way they were answered by
   the adversary; it returns an optimal partial strategy
   (min_path_length as big as possible) continuing from that point,
   until the end of the game *)

let rec opt_strat_from
        (univ : inp list) (x : inp) (qs : int list)
        (inpss : inp list list)
          : strategy =
  if inpss_done x inpss
  then Done
  else Next  (* so qs is not empty *)
       (map
        (fun i ->  (* query i *)
           let ps =           
             map
             (fun a ->  (* answer a *)
                (a,
                 opt_strat_from univ x (remove qs i) (filter_nth inpss i a)))
             univ in
           let (a, strat) =
             optimal (fun (_, strat) -> min_path_length strat) ps in
           (i, a, strat))
        qs)

(* returns an optimal strategy (min_path_length as big as possible)
   for the problem with universe univ, arity arity (>= 1) and where x
   is the element to be searched for *)

let optimal_strategy (univ : inp list) (arity : int) (x : inp) : strategy =
  opt_strat_from univ x (upto arity) (init_inpss univ x arity)

(* if n >= 0, then indent returns the string consisting of n
   spaces *)

let indent (n : int) : string = String.make n ' '

(* display an adversarial strategy using indentation *)

let display (strat : strategy) : unit =
  let rec disp (lev : int) (strat : strategy) : unit =
    match strat with
    | Done    -> printf "%sdone (level = %d)\n" (indent (lev * 2)) lev
    | Next ts ->
        iter
        (fun (i, a, strat) ->
           printf "%s%d %c\n" (indent (lev * 2)) i a;
           disp (lev + 1) strat)
        ts in
  disp 0 strat;
  printf "\nminimum path length: %d\n" (min_path_length strat)

(* command line argument and option processing *)

(* do we just want to learn the minimum path length of an optimal
   strategy? *)

let mpl_ref : bool ref = ref false

let mpl_arg () =
  (mpl_ref := true; ())

let arg_specs =
  [("-mpl", Unit mpl_arg, "Just print minimum path length");
   ("-minimum-path-length", Unit mpl_arg, "Just print minimum path length")]

let anony_args_ref : string list ref = ref []

let anony_args (s : string) =
  (anony_args_ref := (! anony_args_ref) @ [s]; ())

let () =
  parse arg_specs anony_args
  "Usage: strategy [options] univ-size arity element"

let process_size (size : string) : int =
  match (try Some (int_of_string size) with
         | Failure _ -> None) with
  | None   ->
      (eprintf "universe size must be integer: %s\n" size; exit 1)
  | Some n ->
      if n < 1
        then (eprintf "universe size must be at least one: %d\n" n; exit 1)
      else if n > 26
        then (eprintf
              "universe size may not be greater than 26 : %d\n" n; exit 1)
      else n

let process_arity (arity : string) : int =
  match (try Some (int_of_string arity) with
         | Failure _ -> None) with
  | None   ->
      (eprintf "arity must be integer: %s\n" arity; exit 1)
  | Some n ->
      if n < 1
      then (eprintf "arity must be at least one: %d\n" n; exit 1)
      else n

let process_element (univ : inp list) (elt : string) : inp =
  match (try string_to_inp_opt elt with
         | Failure _ -> None) with
  | None     ->
      (eprintf "element to be searched for must be lowercase character: %s\n"
       elt;
       exit 1)
  | Some elt ->
      if mem elt univ
      then elt
      else (eprintf
            "element to be searched for must be member of universe: %c\n"
            elt;
            exit 1)

let () =
  match ! anony_args_ref with
  | [size; arity; elt] ->
      let size  = process_size size in
      let arity = process_arity arity in
      let univ  = List.take size lowers in
      let elt   = process_element univ elt in
      let str   = optimal_strategy univ arity elt in
      if ! mpl_ref
      then printf "minimum path length: %d\n" (min_path_length str)
      else display str
  | _                  ->
      (usage arg_specs "Usage: strategy [options] univ-size arity element";
       exit 1)

  
