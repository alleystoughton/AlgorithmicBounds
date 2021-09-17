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

(* wc : int -> int returns the worst case number of comparisons used
   by merge sort when given a list of size n *)

op wc_wf_rec_def : (int, int) wf_rec_def =
  fun (n : int,            (* input *)
       f : int -> int) =>  (* for recursive calls on < natural numbers *)
  if n <= 1  (* we only care about 1 <= n *)
  then 0
  else f (n %/ 2) + f (n %%/ 2) + n - 1.

(* the actual recursive definition: *)

op wc : int -> int =
  wf_recur
  lt_nat           (* well-founded relation being used *)
  0                (* element to be returned if recursive calls
                      don't respect well-founded relation *)
  wc_wf_rec_def.  (* body of recursive definition *)

lemma wc_eq (n : int) :
  1 <= n => wc n = n * int_log 2 n - (2 ^ (int_log 2 n + 1) - n - 1).
proof.
move : n.
apply (wf_ind lt_nat).
apply wf_lt_nat.
move => /= n IH ge1_n.
case (n = 1) => [-> /= | ne1_n].
rewrite /wc wf_recur 1:wf_lt_nat /wc_wf_rec_def /=.
by rewrite int_log1_eq0 //= expr1.
have ge2_n : 2 <= n by smt().
rewrite /wc wf_recur 1:wf_lt_nat /wc_wf_rec_def.
have -> /= : ! (n <= 1) by smt().
have -> /= : lt_nat (n %/ 2) n by smt().
have -> /= : lt_nat (n %%/ 2) n by smt().
rewrite -/wc.
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

lemma wc_le (n : int) :
  1 <= n => wc n <= n * int_log 2 n.
proof.
move => ge1_n.
rewrite wc_eq // ler_subl_addr ler_addl.
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
  | Sort  of int list
  | List  of int list
  | Cons  of int & term
  | Merge of term & term
  | Cond  of int & int & term & term
].

op is_sort (t : term) : bool =
  with t = Sort xs      => true
  with t = List xs      => false
  with t = Cons i u     => false
  with t = Merge u v    => false
  with t = Cond i j u v => false.

op of_sort (t : term) : int list =
  with t = Sort xs      => xs
  with t = List xs      => []
  with t = Cons i u     => []
  with t = Merge u v    => []
  with t = Cond i j u v => [].

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

op is_cons (t : term) : bool =
  with t = Sort xs      => false
  with t = List xs      => false
  with t = Cons i u     => true
  with t = Merge u v    => false
  with t = Cond i j u v => false.

op of_cons (t : term) : int * term =
  with t = Sort xs      => (0, List [])
  with t = List xs      => (0, List [])
  with t = Cons i u     => (i, u)
  with t = Merge u v    => (0, List [])
  with t = Cond i j u v => (0, List []).

op is_merge (t : term) : bool =
  with t = Sort xs      => false
  with t = List xs      => false
  with t = Cons i u     => false
  with t = Merge u v    => true
  with t = Cond i j u v => false.

op of_merge (t : term) : term * term =
  with t = Sort xs      => (List [], List [])
  with t = List xs      => (List [], List [])
  with t = Cons i u     => (List [], List [])
  with t = Merge u v    => (u, v)
  with t = Cond i j u v => (List [], List []).

op is_cond (t : term) : bool =
  with t = Sort xs      => false
  with t = List xs      => false
  with t = Cons i u     => false
  with t = Merge u v    => false
  with t = Cond i j u v => true.

op of_cond (t : term) : int * int * term * term =
  with t = Sort xs      => (0, 0, List [], List [])
  with t = List xs      => (0, 0, List [], List [])
  with t = Cons i u     => (0, 0, List [], List [])
  with t = Merge u v    => (0, 0, List [], List [])
  with t = Cond i j u v => (i, j, u, v).

op is_cons_of_list (t : term) : bool =
  with t = Sort xs      => false
  with t = List xs      => false
  with t = Cons i u     => is_list u
  with t = Merge u v    => false
  with t = Cond i j u v => false.

op proper_list (xs : int list) : bool =
  xs <> [] /\ uniq xs /\ all (mem range_len) xs.

op disj_lists (xs ys : 'a list) : bool =
  ! has (mem xs) ys /\ ! has (mem ys) xs.

op elems (t : term) : int list =  (* may have duplicates *)
  with t = Sort xs      => xs
  with t = List xs      => xs
  with t = Cons i u     => i :: elems u
  with t = Merge u v    => elems u ++ elems v
  with t = Cond i j u v => elems u ++ elems v.  (* elems u and elems v
                                                   should be permutation
                                                   of each other *)

op proper (t : term) : bool =
  with t = Sort xs      => proper_list xs
  with t = List xs      => proper_list xs
  with t = Cons i u     => proper u /\ ! mem (elems u) i
  with t = Merge u v    =>
    proper u /\ proper v /\ (is_list v => is_list u) /\
    disj_lists (elems u) (elems v)
  with t = Cond i j u v =>
    is_cons_of_list u /\ is_cons_of_list v /\ elems u = elems v.

lemma proper_start :
  proper (Sort range_len).
proof.
rewrite /= /proper_list /range_len.
split; first by rewrite range_ltn 1:ltzE /= 1:ge1_len.
split; first rewrite range_uniq.
by rewrite allP.
qed.

op repr (cmp : int -> int -> bool, t : term) : int list =
  with t = Sort xs      => sort cmp xs
  with t = List xs      => xs
  with t = Cons i u     => i :: repr cmp u
  with t = Merge u v    => merge cmp (repr cmp u) (repr cmp v)
  with t = Cond i j u v =>
    if cmp i j then repr cmp u else repr cmp v.

type step = [  (* result of call to step on term t *)
  | Done                  (* t is fully evaluated - List ... *)
  | Compare of int & int  (* t's evaluation needs answer to query *)
  | Step    of term       (* the step succeeded *)
].

op is_step (s : step) : bool =
  with s = Done        => false
  with s = Compare i j => false
  with s = Step t      => true.

op of_step (s : step) : term =
  with s = Done        => List [1]
  with s = Compare i j => List [1]
  with s = Step t      => t.

op is_compare (s : step) : bool =
  with s = Done        => false
  with s = Compare i j => true
  with s = Step t      => false.

op of_compare (s : step) : int * int =
  with s = Done        => (0, 0)
  with s = Compare i j => (i, j)
  with s = Step t      => (0, 0).

op step (t : term) : step =
  with t = Sort xs      =>
    let mid = size xs %/ 2 in
    Step
    (Merge
     (Sort (take mid xs))   (* size: size xs %/ 2 *)
     (Sort (drop mid xs)))  (* size: size xs %%/ 2 *)
  with t = List xs      => Done
  with t = Cons n u     =>
    let u' = step u in
    if is_step u'
      then Step (Cons n (of_step u'))
    else if is_compare u'
      then u'
    else (* is_list u *)
         Step (List (n :: of_list u))
  with t = Merge u v    =>
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
         else (* is_list u /\ is_list v *)
              if of_list u = []
                then Step v
              else if of_list v = []
                then Step u
              else let i  = head 0 (of_list u) in
                   let ms = behead (of_list u) in
                   let j  = head 0 (of_list v) in
                   let ns = behead (of_list v) in
                   Step (Cond i j
                         (Cons i (Merge (List ms) v))
                         (Cons j (Merge u (List ns))))
  with t = Cond i j u v => Compare i j.

lemma step_done_iff (t : term) :
  step t = Done <=> is_list t.
proof.
elim t => // /#.
qed.

lemma step_compare_iff (t : term, i j : int) :
  step t = Compare i j <=>
  (exists (n : int, u : term),
   t = Cons n u /\ step u = Compare i j) \/
  (exists (u v : term),
   t = Merge u v /\ step u = Compare i j) \/
  (exists (xs : int list, v : term),
   t = Merge (List xs) v /\ step v = Compare i j) \/
  (exists (u v : term), t = Cond i j u v).
proof.
case t.
smt().
smt().
move => n u.
split => [H | /#].
left; exists n u; smt().
move => u v.
split => [/= | /#].
case (is_step (step u)) => [// | not_is_step_u].
case (is_compare (step u)) =>
  [is_compare_u step_u_eq_Compare_i_j | not_is_compare_u].
left; by exists u v.
case (is_step (step v)) => [// | not_is_step_v].
case (is_compare (step v)) =>
  [is_compare_v step_u_eq_Compare_i_j | not_is_compare_v].
right.
have is_list_u : is_list u.
  move : not_is_step_u not_is_compare_u.
  case u; smt().
have [xs ->] : exists xs, u = List xs.
  move : is_list_u.  
  clear not_is_step_u not_is_compare_u.
  (case u; first smt()); last 3 smt().
  move => ys _; by exists ys.
by exists xs v.
smt().
smt().
qed.

op answer (t : term, b : bool) : term option =
  with t = Sort xs      => None  (* should not happen *)
  with t = List xs      => None
  with t = Cons n u     =>
    let u' = answer t b in
    if u' = None  (* should not happen *)
    then None
    else Some (Cons n (oget u'))
  with t = Merge u v    =>
    let u' = answer u b in
    if u' <> None
    then Some (Merge (oget u') v)
    else (* u should be List ... *)
         let v' = answer v b in
         if v' = None
         then None  (* should not happen *)
         else Some (Merge u (oget v'))
  with t = Cond i j u v =>
    if b then Some u else Some v.

lemma square_divide_lt (n : int) :
  2 <= n =>
  (n %/ 2) ^ 2 + (n %%/ 2) ^ 2 < n ^ 2.
proof.
admit.
qed.

(* termination metric for step *)

op metric (t : term) : int =
  with t = Sort xs      => size xs ^ 2
  with t = List xs      => 0
  with t = Cons i u     => metric u + 1
  with t = Merge u v    => 1 + metric u + metric v
  with t = Cond i j u v => 0.

(* here is our algorithm: *)

module Alg : ALG = {
  var term : term

  proc init(aux : aux) : unit = {
    term <- Sort range_len;
  }

  proc make_query_or_report_output() : response = {
    var r : response;
    var step : step;
    var don : bool <- false;
    while (!don) {
      step <- step term;
      if (step = Done \/ is_compare step) {
        don <- true;
      }
      else {
        term <- of_step step;
      }
    }
    if (step = Done) {  (* term = List ... *)
      r <- Response_Report (of_list term);
    }
    else {
      r <- Response_Query (enc (of_compare step));
    }
    return r;
  }

  proc query_result(b : inp) : unit = {
    term <- oget (answer term b);
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
proc.
admit.  (* will need termination metric for while loop *)
qed.

lemma Alg_query_result_ll :
  islossless Alg.query_result.
proof.
proc; auto.
qed.
