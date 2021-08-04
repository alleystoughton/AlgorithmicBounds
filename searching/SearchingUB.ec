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
require import IntDiv2.  (* division by powers of two *)

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
  var mid  : int  (* temporary *)

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

op correct_invar
   (inps : inp list, aux : aux, out_opt : out option,
    queries : int fset, low high : int) : bool =
  0 <= low <= high < arity /\
  mem_in_range inps aux low high /\
  ! mem_in_range inps aux 0 (low - 1) /\
  (forall (k : int), low <= k < high => ! k \in queries) /\
  (low < high => out_opt = None) /\
  (out_opt <> None => out_opt = Some low).

lemma correct_invar_start (inps : inp list, aux : aux) :
  size inps = arity => all (mem univ) inps => good aux inps =>
  correct_invar inps aux None fset0 0 (arity - 1).
proof.
move => correct_size all_in_univ is_good.
progress.
smt(ge1_arity).
smt().
rewrite /mem_in_range.
exists (index aux inps).
smt(index_ge0 index_mem nth_index).
smt().
smt(in_fset0).
qed.

lemma correct_invar_report
      (inps : inp list, aux : aux, queries : int fset, low : int) :
  size inps = arity => all (mem univ) inps =>
  good aux inps =>
  correct_invar inps aux None queries low low =>
  correct_invar inps aux (Some low) queries low low.
proof.
smt().
qed.

lemma correct_invar_new_window_strictly_up
      (inps : inp list, aux : aux, queries : int fset, low high : int) :
  size inps = arity => all (mem univ) inps => good aux inps =>
  low < high => nth witness inps ((low + high) %/ 2) < aux =>
  correct_invar inps aux None queries low high =>
  correct_invar inps aux None
  (queries `|` fset1 ((low + high) %/ 2)) ((low + high) %/ 2 + 1) high.
proof.
move => correct_size all_in_univ is_good lt_low_high lt_nth_inps_mid_aux
        correct_invar_old.
progress; first 5 smt().
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
move => correct_size all_in_univ is_good lt_low_high le_aux_nth_inps_mid
        correct_invar_old.
progress; first 5 smt().
smt(in_fsetU1).
qed.

lemma correct_invar_answer
      (inps : inp list, aux : aux, queries : int fset, low high : int,
       out_opt : out option) :
  size inps = arity => all (mem univ) inps => good aux inps =>
  out_opt <> None => correct_invar inps aux out_opt queries low high =>
  out_opt = f aux inps.
proof.
move => correct_size all_in_univ is_good out_opt_ne_none invar.
smt(f_goodP).
qed.

(* bound part of loop invariant *)

op win_size (low high : int) : int =
  high - low + 1.

op bound_invar (low high stage : int) : bool =
  0 <= low <= high < arity /\
  0 <= stage <= int_log_up 2 arity /\
  win_size low high <= divpow2up arity stage.

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
progress; first 4 smt().
smt(divpow2up_ge2_lt_int_log_up).
rewrite (divpow2up_next_new_lb (win_size low high)) 1:ge1_arity /#.
qed.

lemma bound_invar_new_window_down (low high stage) :
  bound_invar low high stage => low < high =>
  bound_invar low ((low + high) %/ 2) (stage + 1).
proof.
progress; first 4 smt().
smt(divpow2up_ge2_lt_int_log_up).
rewrite (divpow2up_next_new_lb (win_size low high)) 1:ge1_arity /#.
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
rcondt 1; first auto; progress; smt().
sp.
elim* => stage' queries'.
inline Alg.query_result.
sp 1.
if.
auto; progress [-delta].
smt(fcardUindep1).
rewrite correct_invar_new_window_strictly_up // /#.
rewrite bound_invar_new_window_strictly_up // /#.
auto; progress [-delta].
smt(fcardUindep1).
rewrite correct_invar_new_window_down // /#.
rewrite bound_invar_new_window_down // /#.
auto; progress [-delta].
smt(fcards0).
by rewrite correct_invar_start.
rewrite bound_invar_start.
rewrite H7 /=.
have out_opt0_ne_none :out_opt0 <> None.
  move : H3; by rewrite negb_and /= H7.
by rewrite (correct_invar_answer inps{hr} Alg.aux{hr} queries0 low high).
smt().
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
rewrite (G_ll Alg) 1:Alg_init_ll 1:Alg_make_query_or_report_output_ll
        Alg_query_result_ll.
qed.
