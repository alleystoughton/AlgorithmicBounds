(* Application of Adversarial Lower Bounds Framework to Searching in
   Ordered Lists *)

prover quorum=2 ["Z3" "Alt-Ergo"].  (* both provers must succeed on goals *)

timeout 2.  (* can increase *)

(* given a list of size arity at least one element of which is
   equal to k, the algorithm is trying to find the least list
   index such that the list has k at that position

   it can query the values of elements of the list *)

require import AllCore List FSetAux StdOrder IntDiv.
import IntOrder.

require AdvLowerBounds.   (* adversarial lower bounds framework *)
require import AllLists.  (* generating all lists of length over universe *)
require import IntLog.    (* integer logarithms *)
require import IntDiv2.   (* division by powers of two *)

type inp = int.

(* univ consists of min_inp ... max_inp, and there are
   at least two elements *)

op min_inp : inp.
op max_inp : inp.

axiom lt_min_max : min_inp < max_inp.

op univ = range min_inp (max_inp + 1).

lemma univ_size :
  size univ = max_inp - min_inp + 1.
proof.
rewrite size_range ler_maxr.
smt(lt_min_max).
smt().
qed.

lemma min_inp_univ :
  min_inp \in univ.
proof.
rewrite mem_range.
smt(lt_min_max).
qed.

lemma max_inp_univ :
  max_inp \in univ.
proof.
rewrite mem_range.
smt(lt_min_max).
qed.

type out = int.

(* arity can be any positive number (otherwise int_logup 2 arity would
   be meaningless - see our main theorem at end) *)

op arity : {int | 1 <= arity} as ge1_arity.

type aux = int.  (* value to be searched for *)

(* a list xs of size arity of inputs that are in univ is good relative
   to aux iff it contains aux and is sorted in (not-necessarily
   strictly) ascending order (according to the usual total ordering on
   int)

   note that if aux is not in univ, then there will be no input lists
   xs of size arity, all of whose elements are in univ, and where good
   aux xs holds *)

op good (aux : aux, xs : inp list) : bool =
  aux \in xs /\
  forall (i j : int),
  0 <= i <= j < arity => nth witness xs i <= nth witness xs j.

(* here is our searching function, f: *)

op f (aux : aux, xs : inp list) : out option =
  if size xs = arity /\ all (mem univ) xs /\ good aux xs
  then Some (index aux xs)
  else None.

lemma f_good_not_none (aux : aux, xs : inp list) :
  size xs = arity => all (mem univ) xs => good aux xs =>
  f aux xs <> None.
proof.
move => size_eq_xs all_xs_in_univ good_aux_xs.
by rewrite /f size_eq_xs all_xs_in_univ good_aux_xs.
qed.

lemma f_goodP (aux : aux, xs : inp list) :
  size xs = arity => all (mem univ) xs => good aux xs =>
  let i = oget (f aux xs) in
  0 <= i < arity /\ nth witness xs i = aux /\
  (forall (j : int),
   0 <= j < size xs => nth witness xs j = aux => i <= j).
proof.
move => size_eq_xs all_xs_in_univ good_aux_xs /=.
have [i f_aux_eq] : exists (i : int), f aux xs = Some i.
  exists (oget (f aux xs)).
  by rewrite -some_oget /f size_eq_xs all_xs_in_univ good_aux_xs.
rewrite f_aux_eq oget_some.
have -> : i = index aux xs.
  move : f_aux_eq.
  by rewrite {1}/f size_eq_xs all_xs_in_univ good_aux_xs.
have mem_aux_xs : mem xs aux.
  move : good_aux_xs; by rewrite /good.
split; first by rewrite -size_eq_xs index_ge0 /= index_mem.
split; first by rewrite nth_index.
move => j [ge0_j lt_j_size_xs] eq_nth_xs_j_aux.
case (index aux xs <= j) => [// |].
rewrite -ltrNge => lt_j_index.
have // : nth witness xs j <> aux by rewrite before_index.
qed.

lemma f_good_range (aux : aux, xs : inp list) :
  size xs = arity => all (mem univ) xs => good aux xs =>
  0 <= oget (f aux xs) < arity.
proof.
move => size_eq_xs all_xs_in_univ good_aux_xs /=.
have := f_goodP aux xs _ _ _ => //.
qed.

lemma f_good_ge0 (aux : aux, xs : inp list) :
  size xs = arity => all (mem univ) xs => good aux xs =>
  0 <= oget (f aux xs).
proof.
move => size_eq_xs all_xs_in_univ good_aux_xs /=.
have := f_good_range aux xs _ _ _ => //.
qed.

lemma f_good_lt_arity (aux : aux, xs : inp list) :
  size xs = arity => all (mem univ) xs => good aux xs =>
  oget (f aux xs) < arity.
proof.
move => size_eq_xs all_xs_in_univ good_aux_xs /=.
have := f_good_range aux xs _ _ _ => //.
qed.

lemma f_good_nth (aux : aux, xs : inp list) :
  size xs = arity => all (mem univ) xs => good aux xs =>
  nth witness xs (oget (f aux xs)) = aux.
proof.
move => size_eq_xs all_xs_in_univ good_aux_xs /=.
have := f_goodP aux xs _ _ _ => //.
qed.

lemma f_good_best (aux : aux, xs : inp list, j : int) :
  size xs = arity => all (mem univ) xs => good aux xs =>
  0 <= j < size xs => nth witness xs j = aux =>
  oget (f aux xs) <= j.
proof.
move =>
  size_eq_xs all_xs_in_univ good_aux_xs [ge0_j lt_j_sz_xs]
  nth_xs_j_eq_aux.
have [#] _ _ _ H := f_goodP aux xs _ _ _ => //.
by rewrite H.
qed.

clone import AdvLowerBounds as ALB with
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

(* our adversary uses three elements of inp: *)

op a : inp = min_inp.
op b : inp = min_inp + 1.

lemma a_in_univ : a \in univ.
proof. smt(min_inp_univ). qed.

lemma b_in_univ : b \in univ.
proof.
rewrite /b.
rewrite mem_range.
smt(lt_min_max).
qed.

lemma lt_a_b : a < b.
proof. smt(). qed.

(* here is our adversary: *)

module Adv : ADV = {
  (* invariant:
       0 <= win_beg <= win_end < arity /\
       (win_empty =>
        win_beg = win_end /\ win_end < arity - 1) *)

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
        j <- b;  (* our loop invariant won't imply game over *)
      }
      else {
        j <- b; win_empty <- true;
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
proof. smt(). qed.

lemma query_lt_mid_new_size_lb (win_beg win_end i : int) :
  win_beg <= i <= win_end => i < (win_beg + win_end) %%/ 2 =>
  (win_size false win_beg win_end) %%/ 2 <=
  win_size false (i + 1) win_end.
proof. smt(). qed.

lemma query_ge_mid_new_le (win_beg win_end i : int) :
  win_beg <= i <= win_end => win_beg < win_end =>
 (win_beg + win_end) %%/ 2 <= i =>
  win_beg <= i - 1.
proof. smt(). qed.

lemma query_ge_mid_new_size_lb (win_beg win_end i : int) :
  win_beg <= i <= win_end => (win_beg + win_end) %%/ 2 <= i =>
  (win_size false win_beg win_end) %/ 2 <=
  win_size false win_beg (i - 1).
proof. smt(). qed.

(* window invariant *)

op win_invar (win_beg win_end : int, win_empty : bool) : bool =
  0 <= win_beg <= win_end < arity /\
  (win_empty => win_beg = win_end /\ win_end < arity - 1).

(* invariant relating current list of input lists and window *)

op inpss_win_invar
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

op bound_invar
   (win_beg win_end : int, win_empty : bool, stage : int) : bool =
  (win_end = arity - 1 =>
   divpow2up arity stage <= win_size win_empty win_beg win_end) /\
  (win_end < arity - 1 =>
   divpow2 arity stage <= win_size win_empty win_beg win_end).

(*

lemma inpss_win_invar_init :
  inpss_win_invar (init_inpss b) 0 (arity - 1).
proof.
rewrite /inpss_win_invar.
split; first apply inpss_invar_init.
split; first smt(ge1_arity).
move =>
 i [ge0_i le_i_arity_min1] inps sz_inps low_eq_a ith_eq_b high_eq_c.
rewrite /init_inpss.
rewrite mem_filter.
split.
rewrite /good.
split.
rewrite -ith_eq_b mem_nth /#.
smt().
rewrite AllLists.all_lists_arity_have 1:/# 1:/#.
smt(all_nthP mem_nth a_in_univ b_in_univ c_in_univ).
qed.

lemma inpss_win_invar_filter_size1_window_b
      (inpss : inp list list, win_beg win_end : int) :
  inpss_win_invar inpss win_beg win_end => win_beg = win_end =>
  inpss_win_invar (filter_nth inpss win_beg b) win_beg win_end.
proof.
move => [inpss_invar rest_invar] eq_win_beg_win_end.
rewrite /inpss_win_invar.
split; first by apply inpss_invar_filter.
split; first smt().
smt(mem_filter_nth).
qed.

lemma inpss_win_invar_filter_low_a
      (inpss : inp list list, win_beg win_end k : int) :
  inpss_win_invar inpss win_beg win_end => 0 <= k < win_beg =>
  inpss_win_invar (filter_nth inpss k a) win_beg win_end.
proof.
move => [inpss_invar rest_invar] [ge0_k lt_k_win_beg].
rewrite /inpss_win_invar.
split; first by apply inpss_invar_filter.
split; first smt().
smt(mem_filter_nth).
qed.

lemma inpss_win_invar_filter_high_c
      (inpss : inp list list, win_beg win_end k : int) :
  inpss_win_invar inpss win_beg win_end => win_end < k < arity =>
  inpss_win_invar (filter_nth inpss k c) win_beg win_end.
proof.
move => [inpss_invar rest_invar] [lt_win_end_k lt_k_arity].
rewrite /inpss_win_invar.
split; first by apply inpss_invar_filter.
split; first smt().
smt(mem_filter_nth).
qed.

lemma inpss_win_invar_filter_mid_low_a
      (inpss : inp list list, win_beg win_end k : int) :
  inpss_win_invar inpss win_beg win_end => win_beg <= k < win_end =>
  inpss_win_invar (filter_nth inpss k a) (k + 1) win_end.
proof.
move => [inpss_invar rest_invar] [le_win_beg_k lt_k_win_end].
rewrite /inpss_win_invar.
split; first by apply inpss_invar_filter.
split; first smt().
smt(mem_filter_nth).
qed.

lemma inpss_win_invar_filter_mid_high_c
      (inpss : inp list list, win_beg win_end k : int) :
  inpss_win_invar inpss win_beg win_end => win_beg < k <= win_end =>
  inpss_win_invar (filter_nth inpss k c) win_beg (k - 1).
proof.
move => [inpss_invar rest_invar] [le_win_beg_k le_k_win_end].
rewrite /inpss_win_invar.
split; first by apply inpss_invar_filter.
split; first smt().
smt(mem_filter_nth).
qed.

lemma f_uniq (inps : inp list, k : int) :
  size inps = arity => all (mem univ) inps => 0 <= k < arity =>
  (forall (j : int), 0 <= j < k => nth witness inps j = a) =>
  nth witness inps k = b =>
  (forall (j : int), k < j < arity => nth witness inps j = c) =>
  f b inps = Some k.
proof.
move =>
  size_inps all_in_univ [ge0_k lt_k_arity] low_eq_a kth_eq_b high_eq_c.
have good_b_inps : good b inps by smt(mem_nth).
have := f_goodP b inps _ _ _ => //=.
pose i := oget (f b inps).
move => [#] ge0_i lt_i_arity nth_inps_i_eq_b i_min.
have <- : oget (f b inps) = k by smt().
by rewrite -some_oget 1:f_good_not_none.
qed.

op make_uniq_inps (k : int) : inp list =
  nseq k a ++ [b] ++ nseq (arity - k - 1) c.

lemma size_make_uniq_inps (k : int) :
  0 <= k < arity => size (make_uniq_inps k) = arity.
proof.
move => [ge0_k lt_k_arity].
rewrite /make_uniq_inps !size_cat /= !size_nseq /#.
qed.

lemma nth_make_uniq_inps_lt (j k : int) :
  0 <= k => 0 <= j < k =>
  nth witness (make_uniq_inps k) j = a.
proof.
move => ge0_k j_rng.
rewrite /make_uniq_inps.
smt(size_cat size_nseq nth_cat nth_nseq).
qed.

lemma nth_make_uniq_inps_eq (j k : int) :
  0 <= k => nth witness (make_uniq_inps k) k = b.
proof.
move => ge0_k.
rewrite /make_uniq_inps.
smt(size_cat size_nseq nth_cat nth_nseq).
qed.

lemma nth_make_uniq_inps_gt (j k : int) :
  0 <= k => k < j < arity =>
  nth witness (make_uniq_inps k) j = c.
proof.
move => ge0_k j_rng.
rewrite /make_uniq_inps.
smt(size_cat size_nseq nth_cat nth_nseq).
qed.

lemma all_in_univ_make_uniq_inps (k : int) :
  0 <= k < arity => all (mem univ) (make_uniq_inps k).
proof.
move => [ge0_k lt_k_arity].
rewrite /make_uniq_inps !all_cat /= !all_nseq.
smt(a_in_univ b_in_univ c_in_univ).
qed.

lemma good_make_uniq_inps (k : int) :
  0 <= k < arity => good b (make_uniq_inps k).
proof.
move => [ge0_k lt_k_arity].
rewrite /good /make_uniq_inps.
split.
rewrite mem_cat mem_nseq.
left.
rewrite mem_cat.
by right.
smt(size_make_uniq_inps nth_cat nth_nseq size_nseq size_cat).
qed.

lemma f_make_uniq_inps (k : int) :
  0 <= k < arity => f b (make_uniq_inps k) = Some k.
proof.
move => [ge0_k lt_k_arity].
rewrite (f_uniq _ k) 1:size_make_uniq_inps //
        1:all_in_univ_make_uniq_inps //.
rewrite /make_uniq_inps.
smt(nth_cat nth_nseq size_nseq size_cat).
rewrite /make_uniq_inps.
smt(nth_cat nth_nseq size_nseq size_cat).
rewrite /make_uniq_inps.
smt(nth_cat nth_nseq size_nseq size_cat).
qed.

lemma inpss_win_invar_win_size_ge2_implies_not_inpss_done
      (inpss : inp list list, win_beg win_end : int) :
  inpss_win_invar inpss win_beg win_end =>
  win_beg < win_end => ! inpss_done b inpss.
proof.
rewrite /inpss_win_invar =>
  [[#] inpss_inv ge0_win_beg _ lt_win_end_arity invar_body
   lt_win_beg_win_end].
case (inpss_done b inpss) => [contrad | //].
rewrite /inpss_done in contrad.
have /# : Some win_beg = Some (win_beg + 1).
  apply contrad.
  rewrite mapP.
  exists (make_uniq_inps win_beg).
  split.
  rewrite (invar_body win_beg) 1:/# 1:size_make_uniq_inps 1:/# //.
  smt(nth_make_uniq_inps_lt).
  smt(nth_make_uniq_inps_eq).
  smt(nth_make_uniq_inps_gt).
  smt(f_make_uniq_inps).
  rewrite mapP.
  exists (make_uniq_inps (win_beg + 1)).
  split.
  rewrite (invar_body (win_beg + 1)) 1:/# 1:size_make_uniq_inps 1:/# //.
  smt(nth_make_uniq_inps_lt).
  smt(nth_make_uniq_inps_eq).
  smt(nth_make_uniq_inps_gt).
  smt(f_make_uniq_inps).
qed.

lemma inpss_win_invar_done_implies_win_size1
      (inpss : inp list list, win_beg win_end : int) :
  inpss_win_invar inpss win_beg win_end => inpss_done b inpss =>
  win_size win_beg win_end = 1.
proof.
smt(inpss_win_invar_win_size_ge2_implies_not_inpss_done).
qed.

(* now we consider the bound *)

op stage_metric (stage : int) : int =
  divpow2 arity stage.  (* see IntDiv2 *)

(* invariant relating current stage and window size: *)

op stage_win_size_invar (stage win_size : int) : bool =
  stage_metric stage <= win_size.

lemma stage_win_size_invar_win_size1 (stage : int) :
  0 <= stage => stage_win_size_invar stage 1 =>
  int_log 2 arity <= stage.
proof.
smt(divpow2_le1_int_log_le ge1_arity).
qed.

(* we start at stage 0 and with the window size being arity *)

lemma stage_win_size_invar_init :
  stage_win_size_invar 0 arity.
proof.
smt(ge1_arity divpow2_start).
qed.

(* and the next two lemmas are how we move to the next stage,
   possibly with a smaller window size *)

lemma stage_win_size_invar_next_poss_smaller_window
      (stage win_size new_win_size : int) :
  0 <= stage => stage_win_size_invar stage win_size =>
  win_size %/ 2 <= new_win_size =>
  stage_win_size_invar (stage + 1) new_win_size.
proof.
rewrite /stage_win_size_invar /stage_metric.
move => ge0_stage sm_le_ws ws_div2_le_nws.
by rewrite (divpow2_next_new_ub arity stage new_win_size win_size)
           1:ge1_arity.
qed.

lemma stage_win_size_invar_next_same_window (stage win_size : int) :
  0 <= stage => stage_win_size_invar stage win_size =>
  stage_win_size_invar (stage + 1) win_size.
proof.
rewrite /stage_win_size_invar /stage_metric.
move => ge0_stage sm_le_ws.
by rewrite divpow2_next_same_ub 1:ge1_arity.
qed.

(* from the invariants and knowing the game is done, we have our
   bound: *)

lemma inpss_done_lower_bound
      (inpss : inp list list, stage win_beg win_end : int) :
  0 <= stage => inpss_done b inpss =>
  inpss_win_invar inpss win_beg win_end =>
  stage_win_size_invar stage (win_size win_beg win_end) =>
  int_log 2 arity <= stage.
proof.
move => ge0_stage id iwi swsi.
rewrite stage_win_size_invar_win_size1 //.
have <- // : win_size win_beg win_end = 1.
  by rewrite (inpss_win_invar_done_implies_win_size1 inpss).
qed.
*)

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

lemma G_Adv_main (Alg <: ALG{Adv}) :
  hoare [G(Alg, Adv).main : true ==> res.`1 \/ int_log_up 2 arity <= res.`2].
proof.
proc.
seq 7 :
  (inpss = init_inpss aux /\ error = false /\ don = inpss_done aux inpss /\
   stage = 0 /\ queries = fset0 /\ Adv.win_beg = 0 /\
   Adv.win_end = arity - 1 /\ Adv.win_empty = false /\ aux = b).
wp.
call (_ : true).
inline Adv.init.
auto.
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
admit.
admit.
smt().
admit.







rcondf 1
auto; progress [-delta].
print win_invar.





not done and so still multiple possible answers inpss


admit.  (* formulate and use a helper lemma *)




auto; progress [-delta].
by rewrite fcardUindep1.
smt(queries_in_range_add).
rewrite b_in_univ /=.
by apply inpss_win_invar_filter_size1_window_b.
by rewrite stage_win_size_invar_next_same_window 1:fcard_ge0.
if.
auto; progress [-delta].
by rewrite fcardUindep1.
smt(queries_in_range_add).
rewrite a_in_univ /=.
by rewrite inpss_win_invar_filter_low_a.
by rewrite stage_win_size_invar_next_same_window 1:fcard_ge0.
if.
auto; progress [-delta].
by rewrite fcardUindep1.
smt(queries_in_range_add).
rewrite c_in_univ /=.
by rewrite inpss_win_invar_filter_high_c.
by rewrite stage_win_size_invar_next_same_window 1:fcard_ge0.
if.
auto; progress [-delta].
by rewrite fcardUindep1.
smt(queries_in_range_add).
rewrite a_in_univ /=.
rewrite
  (inpss_win_invar_filter_mid_low_a _ Adv.win_beg{hr} _ i{hr})
  // /#.
rewrite
  (stage_win_size_invar_next_poss_smaller_window (card queries)
   (win_size Adv.win_beg{hr} Adv.win_end{hr})
   (win_size (i{hr} + 1) Adv.win_end{hr}))
  1:fcard_ge0 // query_le_mid_new_size_lb /#.
auto; progress [-delta].
by rewrite fcardUindep1.
smt(queries_in_range_add).
rewrite c_in_univ /=.
rewrite
  (inpss_win_invar_filter_mid_high_c _ _ Adv.win_end{hr} i{hr})
  // /#.
rewrite
  (stage_win_size_invar_next_poss_smaller_window (card queries)
   (win_size Adv.win_beg{hr} Adv.win_end{hr})
   (win_size Adv.win_beg{hr} (i{hr} - 1)))
  1:fcard_ge0 // query_gt_mid_new_size_lb /#.
auto.
auto; progress [-delta].
by rewrite fcards0.
by rewrite queries_in_range0.
rewrite inpss_win_invar_init.
rewrite stage_win_size_invar_init.
rewrite negb_and /= in H.
elim H => [inpss_done_b_inpss0 | -> //].
right.
by rewrite (inpss_done_lower_bound inpss0 _ win_beg win_end) 1:fcard_ge0.
qed.

(* here is our main theorem: *)

lemma lower_bound &m :
  exists (Adv <: ADV),
  islossless Adv.init /\ islossless Adv.ans_query /\
  forall (Alg <: ALG{Adv}),
  islossless Alg.init => islossless Alg.make_query =>
  islossless Alg.query_result =>
  Pr[G(Alg, Adv).main() @ &m : res.`1 \/ int_log_up 2 arity <= res.`2] = 1%r.
proof.
exists Adv.
split; first apply Adv_init_ll.
split; first apply Adv_ans_query_ll.
move => Alg Alg_init_ll Alg_make_query_ll Alg_query_result_ll.
byphoare => //.
conseq
  (_ : true ==> true)
  (_ : true ==> res.`1 \/ int_log_up 2 arity <= res.`2) => //.
apply (G_Adv_main Alg).
rewrite (G_ll Alg Adv) 1:Alg_init_ll 1:Alg_make_query_ll
        1:Alg_query_result_ll 1:Adv_init_ll Adv_ans_query_ll.
qed.