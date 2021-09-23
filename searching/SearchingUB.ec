(* Application of Upper Bounds Framework to Searching in Ordered
   Lists *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2021 - Boston University
 * Copyright (c) - 2021 - Carol Chen
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

prover quorum=2 ["Z3" "Alt-Ergo"].  (* both provers must succeed on goals *)

timeout 2.  (* can increase *)

(* given a list of size arity at least one element of which is equal
   to k, the algorithm is trying to find the least list index such
   that the list has k at that position

   it can query the values of elements of the list *)

require import AllCore List FSetAux StdOrder IntDiv.
import IntOrder.

require UpperBounds.     (* upper bounds framework *)
require import IntLog.   (* integer logarithms *)

require import SearchingProb.  (* searching in ordered lists problem *)

clone import UpperBounds as UB with
  type inp <- inp,
  op univ  <- univ,
  op def   <- min_inp,
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

realize univ_uniq. rewrite range_uniq. qed.

realize univ_def. rewrite min_inp_univ. qed.

realize good. smt(). qed.

realize bad. smt(). qed.
(* end of realization *)

(* here is our algorithm: *)

module Alg : ALG = {
  var aux  : aux  (* what we're searching for *)
  var low  : int  (* low <= high; definitely at least one aux at index *)
  var high : int  (* in this range, but no aux at index < low *)

  var mid  : int  (* temporary variable *)

  proc init(aux' : aux) : unit = {
    aux <- aux';
    low <- 0;
    high <- arity - 1;
  }

  proc make_query_or_report_output() : response = {
    var r : response;
    if (low = high) {
      r <- Response_Report low;
    }
    else {  (* low < high *)
      mid <- (low + high) %/ 2;
      r <- Response_Query mid;
    }
    return r;
  }

  proc query_result(x : inp) : unit = {
    if (x < aux) {
      low <- mid + 1;
    }
    else {  (* aux <= x *)
      high <- mid;
    }
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

(* correctness part of loop invariant *)

op mem_in_range (xs : 'a list, y : 'a, i j : int) : bool =
  exists (k : int), i <= k <= j /\ nth witness xs k = y.

op nosmt correct_invar
   (inps : inp list, aux : aux, out_opt : out option,
    queries : int fset, low high : int) : bool =
  0 <= low <= high < arity /\
  mem_in_range inps aux low high /\
  ! mem_in_range inps aux 0 (low - 1) /\
  (forall (k : int), low <= k < high => ! k \in queries) /\
  (low < high => out_opt = None) /\
  (out_opt <> None => out_opt = Some low).

lemma correct_invar_range
      (inps : inp list, aux : aux, out_opt : out option,
       queries : int fset, low high : int) :
  correct_invar inps aux out_opt queries low high =>
  0 <= low <= high < arity.
proof.
by rewrite /correct_invar.
qed.

lemma correct_invar_ge0_low
      (inps : inp list, aux : aux, out_opt : out option,
       queries : int fset, low high : int) :
  correct_invar inps aux out_opt queries low high =>
  0 <= low.
proof.
by rewrite /correct_invar.
qed.

lemma correct_invar_le_low_high
      (inps : inp list, aux : aux, out_opt : out option,
       queries : int fset, low high : int) :
  correct_invar inps aux out_opt queries low high =>
  low <= high.
proof.
by rewrite /correct_invar.
qed.

lemma correct_invar_lt_high_arity
      (inps : inp list, aux : aux, out_opt : out option,
       queries : int fset, low high : int) :
  correct_invar inps aux out_opt queries low high =>
  high < arity.
proof.
by rewrite /correct_invar.
qed.

lemma correct_invar_window_not_queries
      (inps : inp list, aux : aux, out_opt : out option,
       queries : int fset, low high k : int) :
  correct_invar inps aux out_opt queries low high =>
  low <= k < high => ! k \in queries.
proof.
rewrite /correct_invar /#.
qed.

lemma correct_invar_start (inps : inp list, aux : aux) :
  size inps = arity => all (mem univ) inps => good aux inps =>
  correct_invar inps aux None fset0 0 (arity - 1).
proof.
move => correct_size all_in_univ is_good.
rewrite /correct_invar.
split; first smt(ge1_arity).
split.
rewrite /mem_in_range.
exists (index aux inps).
smt(index_ge0 index_mem nth_index).
split => /=; first smt().
smt(in_fset0).
qed.

lemma correct_invar_report
      (inps : inp list, aux : aux, queries : int fset, low : int) :
  size inps = arity => all (mem univ) inps => good aux inps =>
  correct_invar inps aux None queries low low =>
  correct_invar inps aux (Some low) queries low low.
proof.
by rewrite /correct_invar.
qed.

lemma correct_invar_new_window_strictly_up
      (inps : inp list, aux : aux, queries : int fset, low high : int) :
  size inps = arity => all (mem univ) inps => good aux inps =>
  low < high => nth witness inps ((low + high) %/ 2) < aux =>
  correct_invar inps aux None queries low high =>
  correct_invar inps aux None
  (queries `|` fset1 ((low + high) %/ 2)) ((low + high) %/ 2 + 1) high.
proof.
rewrite /correct_invar.
move => correct_size all_in_univ is_good lt_low_high lt_nth_inps_mid_aux.
progress; first 4 smt().
smt(in_fsetU1).
qed.

lemma correct_invar_new_window_down
      (inps : inp list, aux : aux, queries : int fset, low high : int) :
  size inps = arity => all (mem univ) inps => good aux inps =>
  low < high => aux <= nth witness inps ((low + high) %/ 2) =>
  correct_invar inps aux None queries low high =>
  correct_invar inps aux None
  (queries `|` fset1 ((low + high) %/ 2)) low ((low + high) %/ 2).
proof.
move => correct_size all_in_univ is_good lt_low_high le_aux_nth_inps_mid.
rewrite /correct_invar.
progress; first 3 smt().
smt(in_fsetU1).
qed.

lemma correct_invar_answer
      (inps : inp list, aux : aux, queries : int fset, low high : int,
       out_opt : out option) :
  size inps = arity => all (mem univ) inps => good aux inps =>
  out_opt <> None => correct_invar inps aux out_opt queries low high => 
  out_opt = f aux inps.
proof.
move => correct_size all_in_univ is_good out_opt_ne_none.
rewrite /correct_invar =>
  /> ge0_low le_low_high lt_high_arity k le_low_k le_k_high
  nth_inps_k_eq_aux no_aux_lt_low _ lt_low_high_impl_out_opt_eq_none
  out_opt_ne_none_impl_out_opt_eq_some_low.
have eq_low_high : low = high by smt().
have eq_k_low : k = low by smt().
rewrite out_opt_ne_none_impl_out_opt_eq_some_low // nth_inps_k_eq_aux.
rewrite (f_ans _ _ low) // /#.
qed.

(* bound part of loop invariant *)

op win_size (low high : int) : int =
  high - low + 1.

op nosmt bound_invar (low high stage : int) : bool =
  0 <= low <= high < arity /\
  0 <= stage <= int_log_up 2 arity /\
  win_size low high <= divpow2up arity stage.

lemma bound_invar_range (low high stage : int) :
  bound_invar low high stage => 0 <= low <= high < arity.
proof.
by rewrite /bound_invar.
qed.

lemma bound_invar_stage_ge0 (low high stage : int) :
  bound_invar low high stage => 0 <= stage.
proof.
by rewrite /bound_invar.
qed.

lemma bound_invar_le_stage_int_log_up_arity (low high stage : int) :
  bound_invar low high stage => stage <= int_log_up 2 arity.
proof.
by rewrite /bound_invar.
qed.

lemma bound_invar_le_win_siz_divpow2up_arity_stage (low high stage : int) :
  bound_invar low high stage =>
  win_size low high <= divpow2up arity stage.
proof.
by rewrite /bound_invar.
qed.

lemma bound_invar_start :
  bound_invar 0 (arity - 1) 0.
proof.
progress.
smt(ge1_arity).
smt(ge1_arity).
smt(int_log_up_ge0 ge1_arity).
smt(divpow2up_start).
qed.

lemma bound_invar_new_window_strictly_up (low high stage) :
  bound_invar low high stage => low < high =>
  bound_invar ((low + high) %/ 2 + 1) high (stage + 1).
proof.
rewrite /bound_invar; progress; first 3 smt().
have ge2_win_siz : 2 <= win_size low high by smt().
smt(divpow2up_ge2_lt_int_log_up).
rewrite (divpow2up_next_new_lb (win_size low high)) 1:ge1_arity // /#.
qed.

lemma bound_invar_new_window_down (low high stage) :
  bound_invar low high stage => low < high =>
  bound_invar low ((low + high) %/ 2) (stage + 1).
proof.
rewrite /bound_invar; progress; first 3 smt().
smt(divpow2up_ge2_lt_int_log_up).
rewrite (divpow2up_next_new_lb (win_size low high)) 1:ge1_arity // /#.
qed.

(* the main lemma: *)

lemma G_main (aux' : aux, inps' : inp list) :
  hoare
  [G(Alg).main :
   aux = aux' /\ inps = inps' /\ size inps = arity /\
   all (mem univ) inps /\ good aux inps ==>
   res.`1 = f aux' inps' /\ res.`2 <= int_log_up 2 arity].
proof.
proc => /=.
seq 5 :
  (inps = inps' /\ size inps = arity /\ all (mem univ) inps /\
   good aux' inps /\ out_opt = None /\ stage = 0 /\ queries = fset0 /\
   ! error /\ Alg.aux = aux' /\ Alg.low = 0 /\ Alg.high = arity - 1).
inline Alg.init; auto.
while
  (inps = inps' /\ size inps = arity /\ all (mem univ) inps /\
   good aux' inps /\ stage = card queries /\ !error /\ Alg.aux = aux' /\
   correct_invar inps aux' out_opt queries Alg.low Alg.high /\
   bound_invar Alg.low Alg.high stage).
inline Alg.make_query_or_report_output.
if.
sp.
rcondf 1; first auto.
auto; progress [-delta].
by apply correct_invar_report.
sp.
rcondt 1; first auto.
sp.
rcondt 1; first auto; progress.
smt(correct_invar_range).
smt(correct_invar_range).
smt(correct_invar_window_not_queries correct_invar_range).
sp.
elim* => stage' queries'.
inline Alg.query_result.
sp 1.
if.
auto; progress [-delta].
smt(fcardUindep1 correct_invar_window_not_queries correct_invar_range).
rewrite correct_invar_new_window_strictly_up //.
smt(correct_invar_range).
rewrite bound_invar_new_window_strictly_up //.
smt(correct_invar_range).
auto; progress [-delta].
smt(fcardUindep1 correct_invar_window_not_queries correct_invar_range).
rewrite correct_invar_new_window_down //.
smt(correct_invar_range).
by rewrite lerNgt.
rewrite bound_invar_new_window_down //.
smt(correct_invar_range).
auto; progress [-delta].
smt(fcards0).
by rewrite correct_invar_start.
rewrite bound_invar_start.
rewrite H7 /=.
have out_opt0_ne_none : out_opt0 <> None.
  move : H3; by rewrite negb_and /= H7.
by rewrite (correct_invar_answer inps{hr} Alg.aux{hr} queries0 low high).
smt(bound_invar_le_stage_int_log_up_arity).
qed.

(* here is our main theorem: *)

lemma upper_bound &m :
  islossless Alg.init /\ islossless Alg.make_query_or_report_output /\
  islossless Alg.query_result /\
  (forall (aux : aux, inps : inp list),
   size inps = arity => all (mem univ) inps => good aux inps =>
   Pr[G(Alg).main(aux, inps) @ &m :
      res.`1 = f aux inps /\ res.`2 <= int_log_up 2 arity] = 1%r).
proof.
split; first apply Alg_init_ll.
split; first apply Alg_make_query_or_report_output_ll.
split; first apply Alg_query_result_ll.
move => aux' inps' size_inps'_eq_arity all_inps'_in_univ good_aux'_inps'.
byphoare
  (_ :
   aux = aux' /\ inps = inps' /\ size inps = arity /\
   all (mem univ) inps /\ good aux inps ==>
   res.`1 = f aux' inps' /\ res.`2 <= int_log_up 2 arity) => //.
conseq
  (_ : true ==> true)
  (_ :
   aux = aux' /\ inps = inps' /\ size inps = arity /\
   all (mem univ) inps /\ good aux inps ==>
   res.`1 = f aux' inps' /\ res.`2 <= int_log_up 2 arity) => //.
by conseq (G_main aux' inps').
rewrite (G_ll Alg predT) 1:Alg_init_ll 1:Alg_make_query_or_report_output_ll
        Alg_query_result_ll.
qed.
