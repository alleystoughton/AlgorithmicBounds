(* Upper Bound Proof for Binary Search Algorithm *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2021-2024 - Boston University
 * Copyright (c) - 2021 - Carol Chen
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

prover quorum=2 ["Z3" "Alt-Ergo"].  (* both provers must succeed on goals *)

timeout 2.  (* can increase *)

require import AllCore List FSetAux StdOrder IntDiv.
import IntOrder.

require import IntLog.  (* working with bounds involving integer logarithms *)

(* searching in ordered lists problem, including bounds frameworks *)
require import SearchingProb.
import UB.  (* upper bounds theory *)

(* here is our algorithm: *)

module Alg : ALG = {
  var aux  : aux  (* what we're searching for *)
  var low  : int  (* low <= high; definitely at least one aux at index *)
  var high : int  (* in this range, but no aux at index < low *)

  proc init(aux' : aux) : unit = {
    aux <- aux';
    low <- 0;
    high <- arity - 1;
  }

  proc make_query_or_report_output() : response = {
    var r : response;
    var mid : int;
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
    var mid : int <- (low + high) %/ 2;
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

op [smt_opaque] correct_invar
   (inpss : inp list list, aux : aux,
    queries : int fset, low high : int) : bool =
  0 <= low <= high < arity /\
  all  (* this will hold vacuously if Adv makes inpss empty *)
  (fun inps =>
     mem_in_range inps aux low high /\
     ! mem_in_range inps aux 0 (low - 1))
  inpss /\
  (forall (k : int), low <= k < high => ! k \in queries).

lemma correct_invar_range
      (inpss : inp list list, aux : aux,
       queries : int fset, low high : int) :
  correct_invar inpss aux queries low high =>
  0 <= low <= high < arity.
proof.
by rewrite /correct_invar.
qed.

lemma correct_invar_ge0_low
      (inpss : inp list list, aux : aux,
       queries : int fset, low high : int) :
  correct_invar inpss aux queries low high =>
  0 <= low.
proof.
by rewrite /correct_invar.
qed.

lemma correct_invar_le_low_high
      (inpss : inp list list, aux : aux,
       queries : int fset, low high : int) :
  correct_invar inpss aux queries low high =>
  low <= high.
proof.
by rewrite /correct_invar.
qed.

lemma correct_invar_lt_high_arity
      (inpss : inp list list, aux : aux,
       queries : int fset, low high : int) :
  correct_invar inpss aux queries low high =>
  high < arity.
proof.
by rewrite /correct_invar.
qed.

lemma correct_invar_all_have_aux_in_window
      (inpss : inp list list, aux : aux,
       queries : int fset, low high : int) :
  correct_invar inpss aux queries low high =>
  all (fun inps => mem_in_range inps aux low high) inpss.
proof.
rewrite /correct_invar; smt(allP).
qed.

lemma correct_invar_all_below_window_no_aux
      (inpss : inp list list, aux : aux,
       queries : int fset, low high : int) :
  correct_invar inpss aux queries low high =>
  all (fun inps => ! mem_in_range inps aux 0 (low - 1)) inpss.
proof.
rewrite /correct_invar; smt(allP).
qed.

lemma correct_invar_window_not_queries
      (inpss : inp list list, aux : aux,
       queries : int fset, low high k : int) :
  correct_invar inpss aux queries low high =>
  low <= k < high => ! k \in queries.
proof.
rewrite /correct_invar /#.
qed.

lemma correct_invar_start (aux : aux) :
  correct_invar (init_inpss aux) aux fset0 0 (arity - 1).
proof.
rewrite /correct_invar.
split; first smt(ge1_arity).
split; first rewrite allP => inps mem_inps_init_inpss_aux /=.
have aux_in_inps : aux \in inps.
  smt(inpss_invar_init allP inpss_invar_all_good_aux).
have size_inps_eq_arity : size inps = arity.
  smt(inpss_invar_init allP inpss_invar_all_size_arity).
split => [| /#].
rewrite /mem_in_range.
exists (index aux inps).
split.
split => [| _].
rewrite index_ge0.
by rewrite ler_subr_addr -ltzE -size_inps_eq_arity index_mem.
by rewrite nth_index.
smt(in_fset0).
qed.

lemma correct_invar_new_window_strictly_up
      (inpss : inp list list, aux : aux, queries : int fset,
       low high : int, inp : inp) :
  inpss_invar aux inpss => low < high => inp < aux =>
  correct_invar inpss aux queries low high =>
  correct_invar (filter_nth inpss ((low + high) %/ 2) inp) aux
  (queries `|` fset1 ((low + high) %/ 2)) ((low + high) %/ 2 + 1) high.
proof.
move => inpss_invar_aux_inpss lt_low_high lt_inp_aux.
rewrite /correct_invar =>
  [#] ge0_low le_low_high lt_high_arity all_inpss_range_cond
  queries_cond.
split; first smt().
split.
rewrite allP => inps.
rewrite mem_filter /= => [[nth_inps_ind_eq_inp inps_in_inpss]].
rewrite allP in all_inpss_range_cond.
have [aux_in_range aux_not_below_range]
     := all_inpss_range_cond inps _ => //=.
smt(inpss_invar_all_good_aux allP).
smt(in_fsetU1).
qed.

lemma correct_invar_new_window_down
      (inpss : inp list list, aux : aux, queries : int fset,
       low high : int, inp : inp) :
  inpss_invar aux inpss => low < high => aux <= inp =>
  correct_invar inpss aux queries low high =>
  correct_invar (filter_nth inpss ((low + high) %/ 2) inp) aux
  (queries `|` fset1 ((low + high) %/ 2)) low ((low + high) %/ 2).
proof.
move => inpss_invar_aux_inpss lt_low_high le_aux_inp.
rewrite /correct_invar =>
  [#] ge0_low le_low_high lt_high_arity all_inpss_range_cond
  queries_cond.
split; first smt().
split.
rewrite allP => inps.
rewrite mem_filter /= => [[nth_inps_ind_eq_inp inps_in_inpss]].
rewrite allP in all_inpss_range_cond.
have [aux_in_range aux_not_below_range]
     := all_inpss_range_cond inps _ => //=.
smt(inpss_invar_all_good_aux allP).
smt(in_fsetU1).
qed.

lemma correct_invar_answer
      (inpss : inp list list, aux : aux, queries : int fset, low high : int) :
  inpss_invar aux inpss => inpss <> [] => low = high =>
  correct_invar inpss aux queries low high =>
  inpss_answer aux inpss low.
proof.
move => inpss_invar_aux_inpss inpss_nonnil eq_low_high.
rewrite /correct_invar =>
  [#] ge0_low le_low_high lt_high_arity all_inpss_range _.
rewrite /inpss_answer.
split => [// | x].
rewrite mapP => [[inps [inps_in_inpss ->]]].
rewrite (f_ans _ _ low) //.
smt(inpss_invar_all_size_arity allP).
smt(inpss_invar_all_all_mem_univ allP).
smt(inpss_invar_all_good_aux allP).
smt(). smt(allP). smt(allP).
qed.

(* bound part of loop invariant *)

op win_size (low high : int) : int =
  high - low + 1.

op [smt_opaque] bound_invar (low high stage : int) : bool =
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
rewrite -ltzE divpow2up_ge2_lt_int_log_up 1:ge1_arity // /#.
rewrite (divpow2up_next_new_lb (win_size low high)) 1:ge1_arity //.
smt(div2_plus_div2up_eq).
qed.

lemma bound_invar_new_window_down (low high stage) :
  bound_invar low high stage => low < high =>
  bound_invar low ((low + high) %/ 2) (stage + 1).
proof.
rewrite /bound_invar; progress; first 3 smt().
rewrite -ltzE divpow2up_ge2_lt_int_log_up 1:ge1_arity // /#.
rewrite (divpow2up_next_new_lb (win_size low high)) 1:ge1_arity //.
smt(div2_plus_div2up_eq).
qed.

(* the main lemma: *)

lemma G_main (Adv <: ADV{-Alg}) :
  hoare
  [G(Alg, Adv).main :
   true ==>
   ! res.`1 /\ res.`2 <= int_log_up 2 arity].
proof.
proc => /=.
seq 7 :
  (
   aux = Alg.aux /\ inpss = init_inpss aux /\
   !error /\ don = (inpss = []) /\ stage = 0 /\ queries = fset0 /\
   Alg.low = 0 /\ Alg.high = arity - 1).
inline Alg.init; wp.
call (_ : true); first auto.
while
  (aux = Alg.aux /\ stage = card queries /\ inpss_invar aux inpss /\
   (!don => inpss <> []) /\ !error /\
   correct_invar inpss aux queries Alg.low Alg.high /\
   bound_invar Alg.low Alg.high stage).
inline Alg.make_query_or_report_output.
if.
sp.
rcondf 1; first auto.
sp 1.
rcondt 1; first auto; progress [-delta].
smt(correct_invar_answer).
auto.
sp.
rcondt 1; first auto.
sp.
rcondt 1; first auto; progress.
smt(correct_invar_range).
smt(correct_invar_range).
smt(correct_invar_window_not_queries correct_invar_range).
sp; elim* => stage' queries'.
seq 1 :
  (aux = Alg.aux /\ stage' = card queries' /\
   inpss_invar aux inpss /\ inpss <> [] /\ !error /\ !don /\
   correct_invar inpss aux queries' Alg.low Alg.high /\
   Alg.low <> Alg.high /\
   bound_invar Alg.low Alg.high stage' /\
   resp = Response_Query ((Alg.low + Alg.high) %/ 2) /\
   i = oget (dec_response_query resp) /\
   queries = queries' `|` fset1 i /\ stage = stage' + 1).
call (_ : true).
auto; progress [-delta]; smt().
wp.
inline Alg.query_result.
sp 2.
if.
auto; progress [-delta].
smt(fcardUindep1 correct_invar_window_not_queries correct_invar_range).
by rewrite inpss_invar_filter.
rewrite correct_invar_new_window_strictly_up //.
smt(correct_invar_range).
rewrite bound_invar_new_window_strictly_up //.
smt(correct_invar_range).
smt(fcardUindep1 correct_invar_window_not_queries correct_invar_range).
by rewrite inpss_invar_filter.
rewrite correct_invar_new_window_strictly_up //.
smt(correct_invar_range).
rewrite bound_invar_new_window_strictly_up //.
smt(correct_invar_range).
auto; progress [-delta].
smt(fcardUindep1 correct_invar_window_not_queries correct_invar_range).
by rewrite inpss_invar_filter.
rewrite correct_invar_new_window_down //.
smt(correct_invar_range). smt().
rewrite bound_invar_new_window_down //.
smt(correct_invar_range).
smt(fcardUindep1 correct_invar_window_not_queries correct_invar_range).
by rewrite inpss_invar_filter.
rewrite correct_invar_new_window_down //.
smt(correct_invar_range). smt().
rewrite bound_invar_new_window_down //.
smt(correct_invar_range).
auto; progress [-delta].
smt(fcards0).
rewrite inpss_invar_init.
rewrite correct_invar_start.
rewrite bound_invar_start.
smt(bound_invar_le_stage_int_log_up_arity).
qed.

(* here is our main theorem: *)

lemma upper_bound &m :
  islossless Alg.init /\ islossless Alg.make_query_or_report_output /\
  islossless Alg.query_result /\
  (forall (Adv <: ADV{-Alg}) (adv_term_invar : glob Adv -> bool),
   phoare
   [Adv.init : true ==> adv_term_invar (glob Adv)] = 1%r =>
   phoare
   [Adv.ans_query :
    adv_term_invar (glob Adv) ==> adv_term_invar (glob Adv)] = 1%r =>
   Pr[G(Alg, Adv).main() @ &m :
        ! res.`1 /\ res.`2 <= int_log_up 2 arity] = 1%r).
proof.
split; first apply Alg_init_ll.
split; first apply Alg_make_query_or_report_output_ll.
split; first apply Alg_query_result_ll.
move => Adv adv_term_invar adv_init_term adv_ans_query_term.
byphoare
  (_ : true ==> ! res.`1 /\ res.`2 <= int_log_up 2 arity) => //.
conseq
  (_ : true ==> true)
  (_ :
   true ==> ! res.`1 /\ res.`2 <= int_log_up 2 arity) => //.
apply (G_main Adv).
rewrite (G_ll Alg Adv predT adv_term_invar)
        1:Alg_init_ll 1:Alg_make_query_or_report_output_ll
        1:Alg_query_result_ll 1:adv_init_term adv_ans_query_term.
qed.
