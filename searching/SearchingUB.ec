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

require import AllCore List FSetAux StdOrder IntDiv.
import IntOrder.

require import IntLog.  (* integer logarithms *)

(* searching in ordered lists problem, including bounds frameworks *)
require import SearchingProb.  
import UB.  (* upper bounds framework *)

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
    mid <- 0;  (* value doesn't matter, but must initialize *)
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
   (inpss : inp list list, aux : aux,
    queries : int fset, low high : int) : bool =
  0 <= low <= high < arity /\
  all
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
  all
  (fun (inps : inp list) => nth witness inps ((low + high) %/ 2) = inp)
  inpss =>
  correct_invar inpss aux queries low high =>
  correct_invar inpss aux
  (queries `|` fset1 ((low + high) %/ 2)) ((low + high) %/ 2 + 1) high.
proof.
rewrite /correct_invar =>
  inpss_invar_aux_inpss lt_low_high lt_inp_aux
  all_inpss_eq_inp_at_index [#] ci1 ci2 ci3 ci4 ci5.
progress [-delta].
smt(). smt().
rewrite allP => inps inps_in_inpss /=.
rewrite allP in ci4.
have nth_inps_ind_lt_aux : nth witness inps ((low + high) %/ 2) < aux.
  rewrite allP in all_inpss_eq_inp_at_index.
  by rewrite all_inpss_eq_inp_at_index.
have [mir_aux_win not_mir_aux_below_win] := ci4 inps _ => //=.
smt(inpss_invar_all_good_aux allP).
smt(in_fsetU1).
qed.

lemma correct_invar_new_window_down
      (inpss : inp list list, aux : aux, queries : int fset,
       low high : int, inp : inp) :
  inpss_invar aux inpss => low < high => aux <= inp =>
  all
  (fun (inps : inp list) => nth witness inps ((low + high) %/ 2) = inp)
  inpss =>
  correct_invar inpss aux queries low high =>
  correct_invar inpss aux
  (queries `|` fset1 ((low + high) %/ 2)) low ((low + high) %/ 2).
proof.
rewrite /correct_invar =>
  inpss_invar_aux_inpss lt_low_high ge_aux_inp
  all_inpss_eq_inp_at_index [#] ci1 ci2 ci3 ci4 ci5.
progress [-delta].
smt(). smt().
rewrite allP => inps inps_in_inpss /=.
rewrite allP in ci4.
have nth_inps_ind_lt_aux : aux <= nth witness inps ((low + high) %/ 2).
  rewrite allP in all_inpss_eq_inp_at_index.
  by rewrite all_inpss_eq_inp_at_index.
have [mir_aux_win not_mir_aux_below_win] := ci4 inps _ => //=.
smt(inpss_invar_all_good_aux allP).
smt(in_fsetU1).
qed.

lemma correct_invar_answer
      (inpss : inp list list, aux : aux, queries : int fset, low high : int,
       out_opt : out option) :
  inpss_invar aux inpss => low = high =>
  correct_invar inpss aux queries low high => 
  inpss_answer aux inpss low.
proof.
rewrite /correct_invar =>
  inpss_invar_aux_inpss out_opt_ne_none [#] ge0_low le_low_high
  lt_high_arity all_inpss_range _.
rewrite /inpss_answer => x.
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
rewrite -ltzE divpow2up_ge2_lt_int_log_up 1:ge1_arity // /#.
rewrite (divpow2up_next_new_lb (win_size low high)) 1:ge1_arity // /#.
qed.

lemma bound_invar_new_window_down (low high stage) :
  bound_invar low high stage => low < high =>
  bound_invar low ((low + high) %/ 2) (stage + 1).
proof.
rewrite /bound_invar; progress; first 3 smt().
rewrite -ltzE divpow2up_ge2_lt_int_log_up 1:ge1_arity // /#.
rewrite (divpow2up_next_new_lb (win_size low high)) 1:ge1_arity // /#.
qed.

(* the main lemma: *)

lemma G_main (Adv <: ADV{Alg}) :
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
call (_ : true).
auto; progress [-delta].
while
  (aux = Alg.aux /\ stage = card queries /\ inpss_invar aux inpss /\
   !error /\ correct_invar inpss aux queries Alg.low Alg.high /\
   bound_invar Alg.low Alg.high stage).
admit.
auto; progress [-delta].
smt(fcards0).
rewrite inpss_invar_init.
rewrite correct_invar_start.
rewrite bound_invar_start.
smt(bound_invar_le_stage_int_log_up_arity).
qed.


rewrite H7 /=.
have out_opt0_ne_none : out_opt0 <> None.
  move : H3; by rewrite negb_and /= H7.
by rewrite (correct_invar_answer inps{hr} Alg.aux{hr} queries0 low high).
smt(bound_invar_le_stage_int_log_up_arity).



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
