(* find optimal adversarial strategies for searching for the first
   occurrence of a given element in a sorted list, where the list is
   guaranteed to have at least one occurrence of the element; the
   algorithm's goal is to find the index of that first occurrence

   we consider the simplified case where there are only three
   elements, but allow the choice of the arity (number of elements in
   the list) and element to be searched for to be varied *)

open Batteries
open List
open Printf
open Arg

type inp =
  | A | B | C

let inp_to_string (x : inp) : string =
  match x with
  | A -> "A"
  | B -> "B"
  | C -> "C"

let string_to_inp_opt (s : string) : inp option =
  match s with
  | "A" -> Some A
  | "B" -> Some B
  | "C" -> Some C
  | _   -> None

let univ = [A; B; C]  (* preference order *)

(* we have A < B < C: *)

let compare_inp (x : inp) (y : inp) : bool =
  x = A ||
  (x = B && y <> A) ||
  (x = C && y = C)

(* test whether a list of inp's is sorted in (not necessarily
   strictly) ascending order *)

let rec sorted (xs : inp list) : bool =
  match xs with
  | []           -> true
  | [x]          -> true
  | x :: y :: zs -> compare_inp x y && sorted (y :: zs)

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

(* a list is good, relative to x, iff it is sorted and
   has at least one occurrence of x *)

let good (x : inp) (inps : inp list) : bool =
  sorted inps && mem x inps

(* if arity >= 1, then init_inpss x arity is all the `good x` lists of
   length arity *)

let init_inpss (x : inp) (arity : int) =
  filter (good x) (pow univ arity)

(* assuming all elements of inpss have length arity and 0 <= i <
   arity, then filter, keeping just those inps in inpss that have a at
   position i *)

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
  | Done
  | Next of (int *      (* algorithm's query *)
             inp *      (* adversary's answer *)
             strategy)  (* rest of game *)
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

(* opt_strat_from takes in the elememt x to be searched for, the
   result of filtering `init_inpss x` by the queries already asked and
   the way they were answered by the adversary, and the list qs of
   queries that haven't yet been asked; it returns an optimal partial
   strategy (min_path_length as big as possible) continuing from that
   point, until the end of the game *)

let rec opt_strat_from
        (x : inp) (inpss : inp list list)
        (qs : int list) : strategy =
  if inpss_done x inpss
  then Done
  else Next  (* so qs is not empty *)
       (map
        (fun i ->
           let ps =           
             map
             (fun a ->
                (a, opt_strat_from x (filter_nth inpss i a) (remove qs i)))
             univ in
           let (a, strat) =
             optimal (fun (_, strat) -> min_path_length strat) ps in
           (i, a, strat))
        qs)

(* returns an optimal strategy (min_path_length as big as possible)
   for the problem with arity arity (>= 1) and where x is the
   element to be searched for *)

let optimal_strategy (arity : int) (x : inp) : strategy =
  opt_strat_from x (init_inpss x arity) (upto arity)

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
           printf "%s%d %s\n" (indent (lev * 2)) i (inp_to_string a);
           disp (lev + 1) strat)
        ts in
  disp 0 strat;
  printf "\nminimum path length: %d\n" (min_path_length strat)

let mpl_ref : bool ref = ref false

let mpl_arg () =
  (mpl_ref := true; ())

let arg_specs =
  [("-mpl", Unit mpl_arg, "Just print minimum path length");
   ("-minimum-path-length", Unit mpl_arg, "Just print minimum path length")]

let anony_args_ref : string list ref = ref []

let anony_args (s : string) =
  (anony_args_ref := (! anony_args_ref) @ [s]; ())

let () = parse arg_specs anony_args "Usage: strategy [options] arity mid"

let process_arity (arity : string) : int =
  match (try Some (int_of_string arity) with
         | Failure _ -> None) with
  | None   ->
      (eprintf "arity must be integer: %s\n" arity; exit 1)
  | Some n ->
      if n < 1
      then (eprintf "arity must be at least one: %d\n" n; exit 1)
      else n

let process_mid (mid : string) : inp =
  match (try string_to_inp_opt mid with
         | Failure _ -> None) with
  | None     ->
      (eprintf "mid must be element of type inp: %s\n" mid; exit 1)
  | Some mid -> mid

let () =
  match ! anony_args_ref with
  | [arity; mid] ->
      let arity = process_arity arity in
      let mid = process_mid mid in
      let str = optimal_strategy arity mid in
      if ! mpl_ref
      then printf "minimum path length: %d\n" (min_path_length str)
      else display str
  | _           ->
      (usage arg_specs "Usage: strategy [options] arity mid";
       exit 1)
