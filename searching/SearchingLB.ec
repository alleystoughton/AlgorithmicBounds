(* Lower Bound Proof for Searching in Ordered Lists *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2021-2022 - Boston University
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
import LB.  (* lower bounds theory *)

(* our adversary uses two elements of inp: *)

op nosmt a : inp = min_inp.
op nosmt b : inp = min_inp + 1.

lemma a_in_univ : a \in univ.
proof.
rewrite /a.
smt(min_inp_univ).
qed.

lemma b_in_univ : b \in univ.
proof.
rewrite /b mem_range.
smt(lt_min_max).
qed.

lemma lt_a_b : a < b.
proof.
rewrite /a /b /#.
qed.

(* here is our adversary: *)

module Adv : ADV = {
  (* invariant:
       0 <= win_beg <= win_end < arity /\
       (win_empty => win_beg = win_end /\ win_end < arity - 1) *)

  (* window where answers still unclear *)
  var win_beg, win_end : int

  (* when win_beg = win_end and window is empty *)
  var win_empty : bool

  proc init() : aux = {
    win_beg <- 0; win_end <- arity - 1;
    win_empty <- false;
    return b;
  }

  proc ans_query(i : int) : inp = {
    var j : out;

    if (win_empty) {
      j <- witness;  (* answer doesn't matter *)
    }
    elif (i < win_beg) {
      j <- a;
    }
    elif (win_end < i) {
      j <- b;
    }
    (* win_beg <= i <= win_end /\ ! win_empty *)
    elif (win_beg = win_end) {  (* so i = win_beg *)
      if (win_end = arity - 1) {
        j <- b;  (* we could prove game over, but more convenient *)
      }
      else {
        win_empty <- true;
        j <- witness;  (* answer doesn't matter *)
      }
    }
    (* win_beg <= i <= win_end /\ win_beg < win_end*)
    elif (i < (win_beg + win_end) %%/ 2) {  (* < midpoint (as real) *)
      j <- a; win_beg <- i + 1;
    }
    else {  (* >= midpoint (as real) *)
      j <- b; win_end <- i - 1;
    }
    return j;
  }
}.

op win_size (win_empty : bool, win_beg win_end : int) : int =
  win_empty ? 0 : (win_end - win_beg + 1).

lemma win_size_full :
  win_size false 0 (arity - 1) = arity.
proof. smt(). qed.

lemma win_size_empty (win_beg : int) :
  win_size true win_beg win_beg = 0.
proof. smt(). qed.

lemma query_lt_mid_new_le (win_beg win_end i : int) :
  win_beg <= i <= win_end => win_beg < win_end =>
  i < (win_beg + win_end) %%/ 2 =>
  i + 1 <= win_end.
proof. smt(div2_plus_div2up_eq). qed.

lemma query_lt_mid_new_size_lb (win_beg win_end i : int) :
  win_beg <= i <= win_end => i < (win_beg + win_end) %%/ 2 =>
  (win_size false win_beg win_end) %%/ 2 <=
  win_size false (i + 1) win_end.
proof. smt(div2_plus_div2up_eq). qed.

lemma query_ge_mid_new_le (win_beg win_end i : int) :
  win_beg <= i <= win_end => win_beg < win_end =>
 (win_beg + win_end) %%/ 2 <= i =>
  win_beg <= i - 1.
proof. smt(div2_plus_div2up_eq). qed.

lemma query_ge_mid_new_size_lb (win_beg win_end i : int) :
  win_beg <= i <= win_end => (win_beg + win_end) %%/ 2 <= i =>
  (win_size false win_beg win_end) %/ 2 <=
  win_size false win_beg (i - 1).
proof. smt(div2_plus_div2up_eq). qed.

(* window invariant *)

op nosmt win_invar (win_beg win_end : int, win_empty : bool) : bool =
  0 <= win_beg <= win_end < arity /\
  (win_empty => win_beg = win_end /\ win_end < arity - 1).

(* invariant relating current list of input lists and window *)

op nosmt inpss_win_invar
   (inpss : inp list list, win_beg win_end : int,
    win_empty : bool) : bool =
  inpss_invar b inpss /\  (* not necessary, but easier to understand *)
  (! win_empty =>
   (forall (i : int),
    win_beg <= i <= win_end =>
    forall (inps : inp list),
    size inps = arity =>
    (forall (j : int), 0 <= j < i => nth witness inps j = a) =>
    (forall (j : int), i <= j < arity => nth witness inps j = b) =>
    inps \in inpss) /\
   (win_end < arity - 1 =>
    forall (inps : inp list),
    size inps = arity =>
    (forall (j : int),
     0 <= j <= win_end => nth witness inps j = a) =>
    (forall (j : int),
     win_end < j < arity => nth witness inps j = b) =>
    inps \in inpss)).

(* invariant about lower bound *)

op nosmt bound_invar
   (win_beg win_end : int, win_empty : bool, stage : int) : bool =
  (win_end = arity - 1 =>
   divpow2up arity stage <= win_size win_empty win_beg win_end) /\
  (win_end < arity - 1 =>
   divpow2 arity stage <= win_size win_empty win_beg win_end).

(* lemmas about window invariant *)

lemma win_invar_range (win_beg win_end : int, win_empty : bool) :
  win_invar win_beg win_end win_empty =>
  0 <= win_beg <= win_end < arity.
proof.
by rewrite /win_invar.
qed.

lemma win_invar_ge0_win_beg (win_beg win_end : int, win_empty : bool) :
  win_invar win_beg win_end win_empty =>
  0 <= win_beg.
proof.
by rewrite /win_invar.
qed.

lemma win_invar_le_win_beg_win_end (win_beg win_end : int, win_empty : bool) :
  win_invar win_beg win_end win_empty =>
  win_beg <= win_end.
proof.
by rewrite /win_invar.
qed.

lemma win_invar_lt_win_end_arity (win_beg win_end : int, win_empty : bool) :
  win_invar win_beg win_end win_empty =>
  win_end < arity.
proof.
by rewrite /win_invar.
qed.

lemma win_invar_win_empty_implies_eq_win_beg_win_end (win_beg win_end : int) :
  win_invar win_beg win_end true =>
  win_beg = win_end.
proof.
by rewrite /win_invar.
qed.

lemma win_invar_win_empty_implies_lt_win_end_arity_min1
      (win_beg win_end : int) :
  win_invar win_beg win_end true =>
  win_end < arity - 1.
proof.
by rewrite /win_invar.
qed.

lemma win_invar_init :
  win_invar 0 (arity - 1) false.
proof.
rewrite /win_invar /=.
smt(ge1_arity).
qed.

lemma win_invar_not_at_end_nonempty_to_empty (win_end : int) :
  win_invar win_end win_end false => win_end < arity - 1 =>
  win_invar win_end win_end true.
proof.
by rewrite /win_invar /= =>
  [[ge0_win_end lt_win_end_arity]] lt_win_end_arity_min1.
qed.

lemma win_invar_nonempty_query_lt_mid (win_beg win_end : int, i : int) :
  win_invar win_beg win_end false => win_beg < win_end =>
  win_beg <= i <= win_end => i < (win_beg + win_end) %%/ 2 =>
  win_invar (i + 1) win_end false.
proof.
(* smt() will solve this, but nicer to understand why it's true *)
rewrite /win_invar =>
  [#] ge0_win_beg _ lt_win_end_arity /= lt_win_beg_win_end
  [le_win_beg_i le_i_win_end] lt_i_mid.
split => [| //].
split => [/# | _].
by rewrite (query_lt_mid_new_le win_beg).
qed.

lemma win_invar_nonempty_query_ge_mid (win_beg win_end : int, i : int) :
  win_invar win_beg win_end false => win_beg < win_end =>
  win_beg <= i <= win_end => (win_beg + win_end) %%/ 2 <= i =>
  win_invar win_beg (i - 1) false.
proof.
(* smt() will solve this, but nicer to understand why it's true *)
rewrite /win_invar =>
  [#] ge0_win_beg _ lt_win_end_arity /= lt_win_beg_win_end
  [le_win_beg_i le_i_win_end] ge_i_mid.
split => [ | /#].
split => [// | _].
by rewrite (query_ge_mid_new_le _ win_end).
qed.

(* lemmas about inpss window invariant *)

lemma inpss_win_invar_init :
  inpss_win_invar (init_inpss b) 0 (arity - 1) false.
proof.
rewrite /inpss_win_invar /=.
split; first apply inpss_invar_init.
move =>
  i [ge0_i lt_i_arity_min1] inps size_inps
  inps_lt_i_eq_a inps_ge_i_eq_b.
rewrite /init_inpss mem_filter.
split.
rewrite /good.
split.
rewrite -(inps_ge_i_eq_b (arity - 1)).
smt(ge1_arity).
smt(mem_nth ge1_arity).
smt(lt_a_b).
rewrite AllLists.all_lists_arity_have //.
smt(ge1_arity).
rewrite -(all_nthP _ _ witness) => j [ge0_j lt_size_inps].
smt(a_in_univ b_in_univ).
qed.

lemma inpss_win_invar_filter_low_a
      (inpss : inp list list, win_beg win_end k : int) :
  win_invar win_beg win_end false =>
  inpss_win_invar inpss win_beg win_end false => 0 <= k < win_beg =>
  inpss_win_invar (filter_nth inpss k a) win_beg win_end false.
proof.
move =>
  win_inv [/= inpss_invar [bs_from_win_mid as_to_win_end]]
  [ge0_k lt_k_win_beg].
rewrite /inpss_win_invar.
split => [| /=]; first by apply inpss_invar_filter_nth.
split =>
  [i [le_win_beg_i le_i_win_end] inps
   size_inps inps_lt_i_eq_a inps_ge_i_eq_b |
   lt_win_end_arity_min1 inps size_inps inps_le_win_end_eq_a
   inps_gt_win_end_eq_b].
rewrite mem_filter_nth.
rewrite inps_lt_i_eq_a 1:/# /=.
by rewrite (bs_from_win_mid i).
rewrite mem_filter_nth.
rewrite inps_le_win_end_eq_a 1:ge0_k /=.
smt(win_invar_le_win_beg_win_end).
by rewrite as_to_win_end.
qed.

lemma inpss_win_invar_filter_high_b
      (inpss : inp list list, win_beg win_end k : int) :
  win_invar win_beg win_end false =>
  inpss_win_invar inpss win_beg win_end false  => win_end < k < arity =>
  inpss_win_invar (filter_nth inpss k b) win_beg win_end false.
proof.
move =>
  win_inv [/= inpss_invar [bs_from_win_mid as_to_win_end]]
  [lt_win_end_k lt_k_arity].
rewrite /inpss_win_invar.
split => [| /=]; first by apply inpss_invar_filter_nth.
split =>
  [i [le_win_beg_i le_i_win_end] inps
   size_inps inps_lt_i_eq_a inps_ge_i_eq_b |
   lt_win_end_arity_min1 inps size_inps inps_le_win_end_eq_a
   inps_gt_win_end_eq_b].
rewrite mem_filter_nth.
rewrite inps_ge_i_eq_b 1:/# /=.
by rewrite (bs_from_win_mid i).
rewrite mem_filter_nth.
rewrite inps_gt_win_end_eq_b 1:/# /=.
by rewrite as_to_win_end.
qed.

lemma inpss_win_invar_filter_size1_at_end_b (inpss : inp list list) :
  inpss_win_invar inpss (arity - 1) (arity - 1) false =>
  inpss_win_invar (filter_nth inpss (arity - 1) b)
  (arity - 1) (arity - 1) false.
proof.
move => [/= inpss_invar bs_from_win_mid].
rewrite /inpss_win_invar.
split; first by apply inpss_invar_filter_nth.
move =>
  /= i [le_arity_min1_i le_i_arity_min1]
  inps size_inps inps_lt_i_eq_a inps_ge_i_eq_b.
rewrite mem_filter_nth.
rewrite inps_ge_i_eq_b 1:/# /=.
by rewrite (bs_from_win_mid i).
qed.

lemma inpss_win_invar_filter_nonempty_to_empty_any
      (inpss : inp list list, win_end : int, inp : inp) :
  inpss_win_invar inpss win_end win_end false =>
  inpss_win_invar (filter_nth inpss win_end inp) win_end win_end true.
proof.
rewrite /inpss_win_invar /= => [[inpss_invar_inpss _]].
by apply inpss_invar_filter_nth.
qed.

lemma inpss_win_invar_filter_mid_low_a
      (inpss : inp list list, win_beg win_end k : int) :
  win_invar win_beg win_end false => win_beg <= k <= win_end =>
  inpss_win_invar inpss win_beg win_end false =>
  inpss_win_invar (filter_nth inpss k a) (k + 1) win_end false.
proof.
move =>
  win_inv [le_win_beg_k le_k_win_end]
  [/= inpss_invar [bs_from_win_mid as_to_win_end]].
rewrite /inpss_win_invar /=.
split; first by apply inpss_invar_filter_nth.
split =>
  [i [le_k_plus1_i le_i_win_end] inps
   size_inps inps_lt_i_eq_a inps_ge_i_eq_b |
   lt_win_end_arity_min1 inps size_inps inps_le_win_end_eq_a
   inps_gt_win_end_eq_b].
rewrite mem_filter_nth.
rewrite inps_lt_i_eq_a /=.
smt(win_invar_ge0_win_beg).
by rewrite (bs_from_win_mid i) 1:/#.
rewrite mem_filter_nth.
rewrite inps_le_win_end_eq_a /=.
smt(win_invar_ge0_win_beg).
by rewrite as_to_win_end 1:/#.
qed.

lemma inpss_win_invar_filter_mid_high_b
      (inpss : inp list list, win_beg win_end k : int) :
  win_invar win_beg win_end false => win_beg <= k <= win_end =>
  inpss_win_invar inpss win_beg win_end false =>
  inpss_win_invar (filter_nth inpss k b) win_beg (k - 1) false.
proof.
move =>
  win_inv [le_win_beg_k le_k_win_end]
  [/= inpss_invar [bs_from_win_mid _]].
rewrite /inpss_win_invar /=.
split; first by apply inpss_invar_filter_nth.
split =>
  [i [le_win_beg_i le_i_k_min1] inps
   size_inps inps_lt_i_eq_a inps_ge_i_eq_b |
   lt_k_min1_arity_min1 inps size_inps inps_le_k_min1_eq_a
   inps_gt_k_min1_eq_b].
rewrite mem_filter_nth.
rewrite inps_ge_i_eq_b /=.
smt(win_invar_lt_win_end_arity).
by rewrite (bs_from_win_mid i) 1:/#.
rewrite mem_filter_nth.
rewrite inps_gt_k_min1_eq_b 1:/# /=.
rewrite (bs_from_win_mid k) // /#.
qed.

lemma inpss_win_invar_win_empty_filter_any
      (inpss : inp list list, win_beg win_end : int,
       i : int, inp : inp) :
  inpss_win_invar inpss win_beg win_end true => 0 <= i < arity =>
  inpss_win_invar (filter_nth inpss i inp) win_beg win_end true.
proof.
rewrite /inpss_win_invar /=.
smt(inpss_invar_filter_nth).
qed.

(* lemmas about bound invariant *)

lemma bound_invar_init :
  bound_invar 0 (arity - 1) false 0.
proof.
rewrite /bound_invar.
split => [/= | /#].
smt(divpow2up_start win_size_full).
qed.

lemma bound_invar_next_same_ub
      (win_empty : bool, win_beg win_end stage : int) :
  0 <= stage =>
  bound_invar win_beg win_end win_empty stage =>
  bound_invar win_beg win_end win_empty (stage + 1).
proof.
rewrite /bound_invar; progress.
rewrite divpow2up_next_same_ub // ge1_arity.
rewrite divpow2_next_same_ub // 1:ge1_arity /#.
qed.

lemma bound_invar_next_win_empty_true
      (win_empty : bool, win_end stage : int) :
  0 <= stage => win_end <> arity - 1 =>
  bound_invar win_end win_end false stage =>
  bound_invar win_end win_end true (stage + 1).
proof.
rewrite /bound_invar =>
  ge0_stage -> /= lt_arity_min1_impl lt_win_end_arity_min1.
smt(divpow2_le1_next_eq0 ge1_arity).
qed.

lemma bound_invar_next_new_beg (win_beg win_end i stage : int) :
  win_invar win_beg win_end false =>
  win_beg <= i <= win_end => win_beg <> win_end =>
  i < (win_beg + win_end) %%/ 2 => 0 <= stage =>
  bound_invar win_beg win_end false stage =>
  bound_invar (i + 1) win_end false (stage + 1).
proof.
rewrite /bound_invar =>
  win_inv i_btwn_win_beg_win_end neq_win_beg_win_end
  lt_i_win_mid ge0_stage
  [bnd_invar_impl_eq bnd_invar_impl_lt].
split => [eq_win_end_arity_min1 | lt_win_end_arity_min1].
rewrite (divpow2up_next_new_ub (win_size false win_beg win_end)) //.
smt(ge1_arity).
smt(divpow2up_next_new_ub).
rewrite query_lt_mid_new_size_lb /#.
rewrite (divpow2_next_new_ub (win_size false win_beg win_end)) //
        1:ge1_arity 1:bnd_invar_impl_lt //.
by rewrite (ler_trans (win_size false win_beg win_end %%/ 2))
           1:int_div2_le_int_div2_up query_lt_mid_new_size_lb.
qed.

lemma bound_invar_next_new_end (win_beg win_end i stage : int) :
  win_invar win_beg win_end false =>
  win_beg <= i <= win_end => win_beg <> win_end =>
  (win_beg + win_end) %%/ 2 <= i => 0 <= stage =>
  bound_invar win_beg win_end false stage =>
  bound_invar win_beg (i - 1) false (stage + 1).
proof.
rewrite /bound_invar  =>
  win_inv i_btwn_win_beg_win_end neq_win_beg_win_end
  le_win_mid_i ge0_stage
  [bnd_invar_impl_eq bnd_invar_impl_lt].
split => [| _].
smt(win_invar_lt_win_end_arity).
rewrite (divpow2_next_new_ub (win_size false win_beg win_end)) //.
smt(ge1_arity).
case (win_end = arity - 1) =>
  [eq_win_end_arity_min1 | ne_win_end_arity_min1].
by rewrite (ler_trans (divpow2up arity stage)) 1:le_divpow2_divpow2up
           bnd_invar_impl_eq.
have lt_win_end_arity_min1 : win_end < arity - 1.
  smt(win_invar_lt_win_end_arity).
by rewrite bnd_invar_impl_lt.
by rewrite query_ge_mid_new_size_lb.
qed.

(* supporting lemmas for lemmas about when game is done *)

lemma f_poss_as_then_def_bs (inps : inp list, k : int) :
  size inps = arity => all (mem univ) inps => 0 <= k < arity =>
  (forall (j : int), 0 <= j < k => nth witness inps j = a) =>
  (forall (j : int), k <= j < arity => nth witness inps j = b) =>
  f b inps = Some k.
proof.
move => size_inps all_in_univ [ge0_k lt_k_arity] lt_eq_a ge_eq_b.
rewrite (f_ans b inps k) //.
rewrite /good; split.
rewrite -(ge_eq_b k) // 1:mem_nth /#.
smt(lt_a_b).
smt(lt_a_b).
by rewrite (ge_eq_b k).
qed.

(* if 0 <= k < arity, then make an inps such that f b gives us Some
   k *)

op make_least_inps (k : int) : inp list =
  nseq k a ++ nseq (arity - k) b.

lemma size_make_least_inps (k : int) :
  0 <= k < arity => size (make_least_inps k) = arity.
proof.
move => [ge0_k lt_k_arity].
rewrite /make_least_inps size_cat !size_nseq /#.
qed.

lemma nth_make_least_inps_lt_a (j k : int) :
  0 <= j < k < arity =>
  nth witness (make_least_inps k) j = a.
proof.
move => rng_j_k.
rewrite /make_least_inps nth_cat.
smt(nth_cat nth_nseq size_nseq).
qed.

lemma nth_make_least_inps_ge_b (j k : int) :
  0 <= k <= j < arity =>
  nth witness (make_least_inps k) j = b.
proof.
move => rng_k_j.
rewrite /make_least_inps.
smt(nth_cat nth_nseq size_nseq).
qed.

lemma all_in_univ_make_least_inps (k : int) :
  0 <= k < arity => all (mem univ) (make_least_inps k).
proof.
move => [ge0_k lt_k_arity].
rewrite /make_least_inps all_cat !all_nseq.
smt(a_in_univ b_in_univ).
qed.

lemma good_make_least_inps (k : int) :
  0 <= k < arity => good b (make_least_inps k).
proof.
move => [ge0_k lt_k_arity].
rewrite /good /make_least_inps.
split.
rewrite mem_cat.
right.
rewrite mem_nseq /#.
smt(nth_cat nth_nseq size_nseq lt_a_b).
qed.

lemma f_make_least_inps (k : int) :
  0 <= k < arity => f b (make_least_inps k) = Some k.
proof.
move => [ge0_k lt_k_arity].
rewrite (f_poss_as_then_def_bs _ k) //.
by rewrite size_make_least_inps.
by rewrite all_in_univ_make_least_inps.
move => j [ge0_j lt_j_k]; by rewrite nth_make_least_inps_lt_a.
move => j [le_k_j lt_j_arity]; by rewrite nth_make_least_inps_ge_b.
qed.

(* lemmas about when game is done *)

lemma done_when_win_nonempty_implies_win_size_eq1
      (inpss : inp list list, win_beg win_end : int) :
   win_invar win_beg win_end false =>
   inpss_win_invar inpss win_beg win_end false =>
   inpss_done b inpss => win_size false win_beg win_end = 1.
proof.
rewrite /inpss_win_invar /=.
move => win_inv [#] _ inpss_win_invar_mid _.
have win_range : 0 <= win_beg <= win_end < arity.
  smt(win_invar_range).
apply contraLR => ne1_win_siz.
have ge2_win_siz : 2 <= win_size false win_beg win_end by smt().
clear ne1_win_siz.
case (inpss_done b inpss) => [done_inpss | //].
rewrite /inpss_done in done_inpss.
have lt_win_beg_win_end : win_beg < win_end by smt().
have f_b_mli_win_beg_eq : f b (make_least_inps win_beg) = Some win_beg.
  rewrite f_make_least_inps //#.
have mli_win_beg_in_inpss : make_least_inps win_beg \in inpss.
  rewrite (inpss_win_invar_mid win_beg) 1:/#.
  rewrite size_make_least_inps //#.
  move => j [ge0_j lt_j_win_beg].
  rewrite nth_make_least_inps_lt_a /#.
  move => j [le_win_beg_j lt_j_arity].
  rewrite nth_make_least_inps_ge_b /#.
have f_b_mli_win_beg_plus1_eq :
  f b (make_least_inps (win_beg + 1)) = Some (win_beg + 1).
  rewrite f_make_least_inps /#.
have mli_win_beg_plus1_in_inpss :
  make_least_inps (win_beg + 1) \in inpss.
  rewrite (inpss_win_invar_mid (win_beg + 1)) 1:/#.
  rewrite size_make_least_inps // /#.
  move => j [ge0_j lt_j_win_beg_plus1].
  rewrite nth_make_least_inps_lt_a /#.
  move => j [le_win_beg_plus1_j lt_j_arity].
  rewrite nth_make_least_inps_ge_b /#.
have /# : Some win_beg = Some (win_beg + 1).
  apply done_inpss.
  rewrite mapP.
  exists (make_least_inps win_beg) => /#.
  rewrite mapP.
  exists (make_least_inps (win_beg + 1)) => /#.
qed.

lemma done_when_win_not_at_end_implies_win_size_eq0
      (inpss : inp list list, win_beg win_end : int, win_empty : bool) :
   win_invar win_beg win_end win_empty =>
   inpss_win_invar inpss win_beg win_end win_empty =>
   win_end < arity - 1 => inpss_done b inpss =>
   win_size win_empty win_beg win_end = 0.
proof.
move => win_inv inpss_win_inv lt_win_end_arity_min1.
have win_range : 0 <= win_beg <= win_end < arity.
  smt(win_invar_range).
apply contraLR => ne0_win_siz.
have not_win_empty : ! win_empty by smt().
move : win_inv inpss_win_inv ne0_win_siz.
rewrite not_win_empty => win_inv inpss_win_inv ne0_win_siz.
have ge1_win_siz : 1 <= win_size false win_beg win_end by smt().
clear ne0_win_siz not_win_empty.
rewrite /inpss_win_invar /= in inpss_win_inv.
elim inpss_win_inv =>
  _ [inpss_win_invar_mid inpss_win_invar_as_to_win_end'].
have inpss_win_invar_as_to_win_end :
  forall (inps : inp list),
  size inps = arity =>
  (forall (j : int),
   0 <= j && j <= win_end => nth witness inps j = a) =>
  (forall (j : int),
   win_end < j && j < arity => nth witness inps j = b) =>
  inps \in inpss.
  smt().
clear inpss_win_invar_as_to_win_end'.
case (inpss_done b inpss) => [done_inpss | //].
rewrite /inpss_done in done_inpss.
have f_b_mli_win_beg_eq : f b (make_least_inps win_beg) = Some win_beg.
  rewrite f_make_least_inps /#.
have mli_win_beg_in_inpss : make_least_inps win_beg \in inpss.
  rewrite (inpss_win_invar_mid win_beg) 1:/#.
  rewrite size_make_least_inps // /#.
  move => j [ge0_j lt_j_win_beg].
  rewrite nth_make_least_inps_lt_a /#.
  move => j [le_win_beg_j lt_j_arity].
  rewrite nth_make_least_inps_ge_b /#.
have f_b_mli_win_end_plus1_eq :
  f b (make_least_inps (win_end + 1)) = Some (win_end + 1).
  rewrite f_make_least_inps /#.
have mli_win_end_plus1_in_inpss :
  make_least_inps (win_end + 1) \in inpss.
  rewrite inpss_win_invar_as_to_win_end.
  rewrite size_make_least_inps // /#.
  move => j [ge0_j le_j_win_end].
  rewrite nth_make_least_inps_lt_a /#.
  move => j [lt_win_end_j lt_j_arity].
  rewrite nth_make_least_inps_ge_b /#.
have /# : Some win_beg = Some (win_end + 1).
  apply done_inpss.
  rewrite mapP.
  exists (make_least_inps win_beg) => /#.
  rewrite mapP.
  exists (make_least_inps (win_end + 1)) => /#.
qed.

lemma inpss_done_lower_bound
      (inpss : inp list list, stage win_beg win_end : int,
       win_empty : bool) :
  0 <= stage => win_invar win_beg win_end win_empty =>
  inpss_win_invar inpss win_beg win_end win_empty =>
  bound_invar win_beg win_end win_empty stage =>
  inpss_done b inpss => int_log_up 2 arity <= stage.
proof.
rewrite /bound_invar =>
  ge0_stage win_inv inpss_win_inv
  [bound_inv_when_win_end_eq_arity_min1
   bound_inv_when_win_end_lt_arity_min1]
  done_inpss.
case (win_end = arity - 1) =>
  [eq_win_end_arity_min1 | ne_win_end_arity_min1].
have le_dp2u_win_sz :
  divpow2up arity stage <= win_size win_empty win_beg win_end.
  by rewrite bound_inv_when_win_end_eq_arity_min1.
have not_win_empty : ! win_empty.
  smt(win_invar_win_empty_implies_lt_win_end_arity_min1).
have eq1_win_sz : win_size win_empty win_beg win_end = 1.
  smt(done_when_win_nonempty_implies_win_size_eq1).
rewrite divpow2up_eq1_int_log_up_le 1:ge1_arity //.
smt(divpow2up_ge1 ge1_arity).
have lt_win_end_arity_min1 : win_end < arity - 1.
  smt(win_invar_lt_win_end_arity).
have le_dp2_win_sz :
  divpow2 arity stage <= win_size win_empty win_beg win_end.
  by rewrite bound_inv_when_win_end_lt_arity_min1.
have eq1_win_sz : win_size win_empty win_beg win_end = 0.
  smt(done_when_win_not_at_end_implies_win_size_eq0).
rewrite divpow2_eq0_int_log_up_le 1:ge1_arity //.
smt(divpow2_ge0 ge1_arity).
qed.

(* adversary is lossless *)

lemma Adv_init_ll : islossless Adv.init.
proof.
proc; auto.
qed.

lemma Adv_ans_query_ll : islossless Adv.ans_query.
proof.
proc; auto.
qed.

(* the main lemma *)

lemma G_Adv_main (Alg <: ALG{-Adv}) :
  hoare [G(Alg, Adv).main : true ==> res.`1 \/ int_log_up 2 arity <= res.`2].
proof.
proc.
seq 7 :
  (inpss = init_inpss aux /\ error = false /\ don = inpss_done aux inpss /\
   stage = 0 /\ queries = fset0 /\ Adv.win_beg = 0 /\
   Adv.win_end = arity - 1 /\ Adv.win_empty = false /\ aux = b).
wp.
call (_ : true).
inline Adv.init; auto.
while
  (stage = card queries /\ queries_in_range queries /\
   don = inpss_done aux inpss /\
   win_invar Adv.win_beg Adv.win_end Adv.win_empty /\
   inpss_win_invar inpss Adv.win_beg Adv.win_end Adv.win_empty /\
   bound_invar Adv.win_beg Adv.win_end Adv.win_empty stage).
seq 1 :
  (stage = card queries /\ queries_in_range queries /\
   don = inpss_done aux inpss /\ !don /\ !error /\
   win_invar Adv.win_beg Adv.win_end Adv.win_empty /\
   inpss_win_invar inpss Adv.win_beg Adv.win_end Adv.win_empty /\
   bound_invar Adv.win_beg Adv.win_end Adv.win_empty stage).
call (_ : true); first auto.
if.
wp.
call (_ : true); first auto.
sp; elim* => stage queries.
inline Adv.ans_query.
sp 1.
if.
auto; progress [-delta].
smt(fcardUindep1).
smt(queries_in_range_add).
smt(inpss_win_invar_win_empty_filter_any).
smt(bound_invar_next_same_ub fcard_ge0).
if.
auto; progress [-delta].
smt(fcardUindep1).
smt(queries_in_range_add).
smt(inpss_win_invar_filter_low_a a_in_univ).
smt(bound_invar_next_same_ub fcard_ge0).
if.
auto; progress [-delta].
smt(fcardUindep1).
smt(queries_in_range_add).
smt(inpss_win_invar_filter_high_b b_in_univ).
smt(bound_invar_next_same_ub fcard_ge0).
if.
if.
auto; progress [-delta].
smt(fcardUindep1).
smt(queries_in_range_add).
smt(inpss_win_invar_filter_size1_at_end_b b_in_univ).
smt(bound_invar_next_same_ub fcard_ge0).
auto; progress [-delta].
smt(fcardUindep1).
smt(queries_in_range_add).
smt(win_invar_not_at_end_nonempty_to_empty).
smt(inpss_win_invar_filter_nonempty_to_empty_any).
smt(bound_invar_next_win_empty_true fcard_ge0).
if.
auto; progress [-delta].
smt(fcardUindep1).
smt(queries_in_range_add).
smt(win_invar_nonempty_query_lt_mid).
smt(inpss_win_invar_filter_mid_low_a a_in_univ).
smt(bound_invar_next_new_beg fcard_ge0).
auto; progress [-delta].
smt(fcardUindep1).
smt(queries_in_range_add).
have -> : Adv.win_empty{hr} = false by smt().
rewrite (win_invar_nonempty_query_ge_mid _ Adv.win_end{hr}) /#.
have -> : Adv.win_empty{hr} = false by smt().
rewrite (inpss_win_invar_filter_mid_high_b _ _ Adv.win_end{hr} i{hr}) /#.
have -> : Adv.win_empty{hr} = false by smt().
rewrite (bound_invar_next_new_end _ Adv.win_end{hr}) // 4:fcard_ge0 /#.
auto.
auto; progress [-delta].
smt(fcards0).
smt(queries_in_range0).
rewrite win_invar_init.
rewrite inpss_win_invar_init.
rewrite bound_invar_init.
rewrite negb_and /= in H.
elim H => [inpss_done_inpss0 | -> //].
right.
smt(inpss_done_lower_bound fcard_ge0).
qed.

(* here is our main theorem: *)

lemma lower_bound &m :
  exists (Adv <: ADV),
  islossless Adv.init /\ islossless Adv.ans_query /\
  forall (Alg <: ALG{-Adv}) (alg_term_invar : (glob Alg) -> bool),
  phoare
  [Alg.init : true ==> alg_term_invar (glob Alg)] = 1%r =>
  phoare
  [Alg.make_query :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r =>
  phoare
  [Alg.query_result :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r =>
  Pr[G(Alg, Adv).main() @ &m : res.`1 \/ int_log_up 2 arity <= res.`2] = 1%r.
proof.
exists Adv.
split; first apply Adv_init_ll.
split; first apply Adv_ans_query_ll.
move =>
  Alg alg_term_invar Alg_init_term Alg_make_query_term Alg_query_result_term.
byphoare => //.
conseq
  (_ : true ==> true)
  (_ : true ==> res.`1 \/ int_log_up 2 arity <= res.`2) => //.
apply (G_Adv_main Alg).
rewrite (G_ll Alg Adv alg_term_invar predT)
        1:Alg_init_term 1:Alg_make_query_term 1:Alg_query_result_term
        1:Adv_init_ll Adv_ans_query_ll.
qed.
