(* Application of Upper Bounds Framework to Comparison-based
   Sorting *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2021 - Boston University
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

prover quorum=2 ["Alt-Ergo" "Z3"].

timeout 2.  (* can increase *)

(* the algorithm is trying to figure out how a list of distinct
   elements of size len should be permuted in order to be sorted

   it can ask queries of the form (i, j), for 0 <= i, j < len,
   asking whether the ith element of the list is less-than-or-equal-to
   the jth element (the answer is true or false); it can't ask
   questions about the values of the list elements themselves *)

require import AllCore List IntDiv StdOrder IntMin FSetAux Perms Binomial WF.
import IntOrder.

require UpperBounds.       (* adversarial lower bounds framework *)
require import ListSizes.  (* showing uniq lists have the same size *)
require import AllLists.   (* generating all lists of length over universe *)
require import IntLog.     (* integer logarithms *)

require import SortingProb.  (* comparison-based sorting problem *)

clone import UpperBounds as UB with
  type inp <- inp,
  op univ  <- univ,
  op def   <- true,
  type out <- out,
  op arity <- arity,
  type aux <- aux,
  op good  <- good,
  op f     <- f
proof *.
(* beginning of realization *)
realize ge0_arity.
rewrite (lez_trans 1) // ge1_arity.
qed.

realize univ_uniq. by rewrite /univ. qed.

realize univ_def. by rewrite /univ. qed.

realize good. smt(f_is_some). qed.

realize bad.
move => aux xs H.
have not_tot_ord_xs : ! total_ordering xs.
  elim H; first smt(total_ordering_size).
  elim; first smt(allP).
  smt().
by rewrite f_bad.
qed.
(* end of realization *)

require import AllCore List IntDiv StdOrder.
import IntOrder.

(* num : int -> int returns the worst case number of comparisons used
   by merge sort when given a list of size n *)

op num_wf_rec_def : (int, int) wf_rec_def =
  fun (n : int,            (* input *)
       f : int -> int) =>  (* for recursive calls on < natural numbers *)
  if n <= 1  (* we only care about 1 <= n *)
  then 0
  else f (n %/ 2) + f (n %%/ 2) + n - 1.

(* the actual recursive definition: *)

op num : int -> int =
  wf_recur
  lt_nat           (* well-founded relation being used *)
  0                (* element to be returned if recursive calls
                      don't respect well-founded relation *)
  num_wf_rec_def.  (* body of recursive definition *)

lemma num_eq (n : int) :
  1 <= n => num n = n * int_log 2 n - (2 ^ (int_log 2 n + 1) - n - 1).
proof.
move : n.
apply (wf_ind lt_nat).
apply wf_lt_nat.
move => /= n IH ge1_n.
case (n = 1) => [-> /= | ne1_n].
rewrite /num wf_recur 1:wf_lt_nat /num_wf_rec_def /=.
by rewrite int_log1_eq0 //= expr1.
have ge2_n : 2 <= n by smt().
rewrite /num wf_recur 1:wf_lt_nat /num_wf_rec_def.
have -> /= : ! (n <= 1) by smt().
have -> /= : lt_nat (n %/ 2) n by smt().
have -> /= : lt_nat (n %%/ 2) n by smt().
rewrite -/num.
rewrite (IH (n %/ 2)) 1:/# 1:/#.
rewrite (IH (n %%/ 2)) 1:/# 1:/#.
rewrite int_log_div //=.
have -> :
  n %/ 2 * (int_log 2 n - 1) - (2 ^ int_log 2 n - n %/ 2 - 1) =
  n %/ 2 * int_log 2 n - 2 ^ (int_log 2 n) + 1 by algebra.
have -> :
 n %%/ 2 * int_log 2 (n %%/ 2) -
 (2 ^ (int_log 2 (n %%/ 2) + 1) - n %%/ 2 - 1) =
 n %%/ 2 * int_log 2 (n %%/ 2) -
 2 ^ (int_log 2 (n %%/ 2) + 1) + n %%/ 2 + 1 by algebra.
have -> :
  n * int_log 2 n - (2 ^ (int_log 2 n + 1) - n - 1) =
  n * int_log 2 n - 2 ^ (int_log 2 n + 1) + 1 + n by algebra.
have -> :
  n %/ 2 * int_log 2 n - 2 ^ int_log 2 n + 1 +
  (n %%/ 2 * int_log 2 (n %%/ 2) -
   2 ^ (int_log 2 (n %%/ 2) + 1) + n %%/ 2 + 1) +
  n - 1 =
  n %/ 2 * int_log 2 n - 2 ^ int_log 2 n +
  n %%/ 2 * int_log 2 (n %%/ 2) - 2 ^ (int_log 2 (n %%/ 2) + 1)
  + n %%/ 2 + 1 + n by algebra.
rewrite -subr_eq addrK.
rewrite -subr_eq addrK.
have [lt | eq] :
  n < 2 ^ (int_log 2 n + 1) - 1 \/ n = 2 ^ (int_log 2 n + 1) - 1.
  smt(int_log_ub_lt).
rewrite int_log2_divup_min1 //=.
have -> :
  n %/ 2 * int_log 2 n - 2 ^ int_log 2 n +
  n %%/ 2 * (int_log 2 n - 1) - 2 ^ int_log 2 n + n %%/ 2 =
  n %/ 2 * int_log 2 n + n %%/ 2 * int_log 2 n -
  (2 ^ int_log 2 n + 2 ^ int_log 2 n) by algebra.
by rewrite -mul2l -exprS 1:int_log_ge0 // -subr_eq addrK -mulrDl
           -div2_plus_div2up_eq.
rewrite int_log2_divup_eq //.
have -> :
  n %/ 2 * int_log 2 n - 2 ^ int_log 2 n + n %%/ 2 * int_log 2 n -
  2 ^ (int_log 2 n + 1) + n %%/ 2 =
  (n %/ 2 + n %%/ 2) * int_log 2 n + n %%/ 2
  - 2 ^ int_log 2 n - 2 ^ (int_log 2 n + 1) by algebra.
rewrite -subr_eq addrK -div2_plus_div2up_eq -addrA.
have -> // : n %%/ 2 - 2 ^ int_log 2 n = 0.
rewrite subr_eq /= int_div_up2_odd 1:eq /=.
by rewrite odd_iff_plus1_even /= exprS 1:int_log_ge0 // dvdz_mulr.
by rewrite {1}eq /= exprS 1:int_log_ge0 // mulKz.
qed.

lemma num_le (n : int) :
  1 <= n => num n <= n * int_log 2 n.
proof.
move => ge1_n.
rewrite num_eq // ler_subl_addr ler_addl.
smt(int_log_ub_lt).
qed.

op merge (cmp : 'a -> 'a -> bool, xs ys : 'a list) : 'a list =
  with xs = [],      ys = []      => []
  with xs = [],      ys = _ :: _  => ys
  with xs = _ :: _,  ys = []      => xs
  with xs = u :: us, ys = v :: vs =>
    if cmp u v
    then u :: merge cmp us ys
    else v :: merge cmp xs vs.

lemma cmp_head_merge (cmp : 'a -> 'a -> bool, n : 'a, xs ys : 'a list) :
  cmp n (head n xs) => cmp n (head n ys) =>
  cmp n (head n (merge cmp xs ys)).
proof.
case xs => [| u us].
by case ys.
case ys => [// | v vs /=].
by case (cmp u v).
qed.

lemma merge_sorted (e : 'a -> 'a -> bool, xs ys : 'a list) :
  (forall (a : 'a), e a a) =>
  (forall (a b : 'a), e a b \/ e b a) =>
  sorted e xs => sorted e ys =>
  sorted e (merge e xs ys).
proof.
move => refl_e tot_e; move : ys.
elim xs => [| u us IH_outer].
by case.
elim => [// | v vs /= IH_inner path_u_us path_v_vs].
case (e u v) => [e_u_v | not_e_u_v].
rewrite (pathP u); right; split => [| /=].
by rewrite cmp_head_merge cmp_head_path_same_def.
by rewrite IH_outer (path_sorted _ u).
rewrite (pathP v); right; split => [| /=].
rewrite cmp_head_merge cmp_head_path_same_def //= path_u_us /= 1:/#.
by rewrite IH_inner // (path_sorted _ v).
qed.

type term = [
  | Sort  of int list  (* list is nonempty *)
  | List  of int list
  | Cons  of int & term
  | Merge of term & term
  | Cond  of int & int & term & term
].

op deft : term = List [].

op repr (cmp : int -> int -> bool, t : term) : int list =
  with t = Sort xs      => sort cmp xs
  with t = List xs      => xs
  with t = Cons i u     => i :: repr cmp u
  with t = Merge u v    => merge cmp (repr cmp u) (repr cmp v)
  with t = Cond i j u v =>
    if cmp i j then repr cmp u else repr cmp v.

op is_list (t : term) : bool =
  with t = Sort xs      => false
  with t = List xs      => true
  with t = Cons i u     => false
  with t = Merge u v    => false
  with t = Cond i j u v => false.

op of_list (t : term) : int list =
  with t = Sort xs      => []
  with t = List xs      => xs
  with t = Cons i u     => []
  with t = Merge u v    => []
  with t = Cond i j u v => [].

type step = [
  | Stuck
  | Step    of term
  | Compare of int & int
].

op is_step (s : step) : bool =
  with s = Stuck       => false
  with s = Step t      => true
  with s = Compare i j => false.

op of_step (s : step) : term =
  with s = Stuck       => deft
  with s = Step t      => t
  with s = Compare i j => deft.

op is_compare (s : step) : bool =
  with s = Stuck       => false
  with s = Step t      => false
  with s = Compare i j => true.

op of_compare (s : step) : int * int =
  with s = Stuck       => (0, 0)
  with s = Step t      => (0, 0)
  with s = Compare i j => (i, j).

op step (t : term) : step =
  with t = Sort xs =>
    let mid = size xs %/ 2 in
    Step
    (Merge (Sort (take mid xs))  (* size: size xs %/ 2 *)
    (Sort (drop mid xs)))        (* size: size xs %%/ 2 *)
  with t = List xs => Stuck
  with t = Cons n u =>
    let u' = step u in
    if is_step u'
      then Step (Cons n (of_step u'))
    else if is_compare u'
      then u'
    else if is_list u
      then Step (List (n :: of_list u))
    else Stuck
  with t = Merge u v =>
    let u' = step u in
    if is_step u'
      then Step (Merge (of_step u') v)
    else if is_compare u'
      then u'
    else let v' = step v in
         if is_step v'
           then Step (Merge u (of_step v'))
         else if is_compare v'
           then v'
         else if is_list u /\ is_list v
           then if of_list u = []
                  then Step v
                else if of_list v = []
                  then Step u
                else let i = head 0 (of_list u) in
                     let ms = behead (of_list u) in
                     let j = head 0 (of_list v) in
                     let ns = behead (of_list v) in
                     Step (Cond i j
                           (Cons i (Merge (List ms) v))
                           (Cons j (Merge u (List ns))))
         else Stuck
  with t = Cond i j u v => Compare i j.

op answer (t : term, b : bool) : term option =
  with t = Sort xs => None
  with t = List xs => None
  with t = Cons n u =>
    let u' = answer t b in
    if u' = None then None else Some (Cons n (oget u'))
  with t = Merge u v =>
    let u' = answer u b in
    if u' <> None
    then Some (Merge (oget u') v)
    else let v' = answer v b in
         if v' = None then None else Some (Merge u (oget v'))
  with t = Cond i j u v =>
    if b then Some u else Some v.

(* here is our algorithm: *)

module Alg : ALG = {
  proc init(aux : aux) : unit = {
  }

  proc make_query_or_report_output() : response = {
    var r : response;
    return r;
  }

  proc query_result(x : inp) : unit = {
  }
}.

(* algorithm is lossless *)

lemma Alg_init_ll : islossless Alg.init.
proof.
proc; auto.
qed.

lemma Alg_make_query_or_report_output_ll :
  islossless Alg.make_query_or_report_output.
proof.
proc; auto.
qed.

lemma Alg_query_result_ll :
  islossless Alg.query_result.
proof.
proc; auto.
qed.
