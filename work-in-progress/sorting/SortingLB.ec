(* Application of Adversarial Lower Bounds Framework to
   Comparison-based Sorting *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020-2021 - Boston University
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

require import AllCore List IntDiv StdOrder IntMin FSetAux.
import IntOrder.

require AdvLowerBounds.   (* adversarial lower bounds framework *)
require import AllLists.  (* generating all lists of length over universe *)
require import IntLog.    (* integer logarithms *)
require import IntDiv2.   (* division by powers of two *)

op len : int.

axiom ge1_len : 1 <= len.

lemma gt0_len : 0 < len.
proof.
rewrite (ltr_le_trans 1) // ge1_len.
qed.

(* to represent this problem using our framework, we encode queries
   (i, j), for 0 <= i, j < len, as integers between 0 and arity - 1,
   for arity = len * len: *)

op arity : int = len * len.

lemma ge1_arity : 1 <= arity.
proof.
rewrite /arity mulr_ege1 ge1_len.
qed.

(* enc and dec take us back and forth between pairs (i, j) : int *
   int, were 0 <= i, j < len, and m : int, where 0 <= m < arity *)

op nosmt enc (p : int * int) : int = p.`1 * len + p.`2.

op nosmt dec (n : int) : int * int = (n %/ len, n %% len).

lemma enc_bounds (p : int * int) :
  0 <= p.`1 < len => 0 <= p.`2 < len =>
  0 <= enc p < arity.
proof.
have ge0_len : 0 <= len by rewrite (ler_trans 1) // ge1_len.
rewrite /arity /enc /=.
case p => i j /=.
move => [ge0_i lt_i_len] [ge0_j lt_j_len].
split => [| _].
by rewrite addr_ge0 1:mulr_ge0.
have le_i_len_min1 : i <= len - 1 by rewrite -ltzS.
rewrite (ler_lt_trans ((len - 1) * len + j)) 1:ler_add
        1:ler_pmul //.
have -> : (len - 1) * len + j = len * len + j - len by algebra.
by rewrite -addrA ltr_snaddr // 1:subr_lt0.
qed.

lemma encK (p : int * int) :
  0 <= p.`1 < len => 0 <= p.`2 < len => dec (enc p) = p.
proof.
rewrite /enc /dec /=.
case p => i j /= [ge0_i lt_i_len] [ge0_j lt_j_len].
split.
rewrite divzMDl 1:lt0r_neq0 1:gt0_len //.
by rewrite divz_small // ge0_j /= ltr_normr lt_j_len.
by rewrite dvdz_modzDl /(%|) 1:modzMl // pmod_small 1:ge0_j.
qed.

lemma dec_bounds_left (m : int) :
  0 <= m < arity => 0 <= (dec m).`1 < len.
proof.
rewrite /arity /dec /= => [[ge0_m lt_m_len_sq]].
split => [| _].
rewrite divz_ge0 1:(ltr_le_trans 1) // ge1_len.
rewrite ltz_divLR 1:(ltr_le_trans 1) // ge1_len.
qed.

lemma dec_bounds_right (m : int) :
  0 <= m < arity => 0 <= (dec m).`2 < len.
proof.
rewrite /arity /dec /= => [[ge0_m lt_m_len_sq]].
split => [| _].
by rewrite modn_ge0.
rewrite ltz_pmod gt0_len.
qed.

lemma decK (m : int) :
  0 <= m < arity => enc (dec m) = m.
proof.
rewrite /enc /dec /=.
move => [ge0_m lt_m_arity].
by rewrite -divz_eq.
qed.

(* we can represent a total ordering on list indices between 0 and len
   - 1 as a list of booleans of size arity *)

type inp = bool.

op univ : inp list = [true; false].  (* so no restriction *)

(* assuming size xs = arity, 0 <= i < len and 0 <= j < len, rel xs i j
   tests whether i is less-than-or-equal-to j in the relation xs *)

op rel (xs : inp list, i j : int) : bool =
  nth false xs (enc (i, j)).

op nosmt total_ordering (xs : inp list) : bool =
  size xs = arity /\
  (* reflexive *)
  (forall (i : int), 0 <= i < len => rel xs i i) /\
  (* transitive *)
  (forall (i j k : int),
   0 <= i < len => 0 <= j < len => 0 <= k < len => 
   rel xs i j => rel xs j k => rel xs i k) /\
  (* antisymmetric *)
  (forall (i j : int),
   0 <= i < len => 0 <= j < len =>
   rel xs i j => rel xs j i => i = j) /\
  (* total *)
  (forall (i j : int),
   0 <= i < len => 0 <= j < len => i <> j =>
   rel xs i j \/ rel xs j i).
  
lemma total_ordering_size (xs : inp list) :
  total_ordering xs => size xs = arity.
proof. rewrite /total_ordering /#. qed.

lemma total_ordering_refl (xs : inp list, i : int) :
  total_ordering xs => 0 <= i < len => rel xs i i.
proof. rewrite /total_ordering /#. qed.

lemma total_ordering_trans (xs : inp list, j i k : int) :
  total_ordering xs =>
  0 <= j < len => 0 <= i < len => 0 <= k < len =>
  rel xs i j => rel xs j k => rel xs i k.
proof. rewrite /total_ordering /#. qed.

lemma total_ordering_antisym (xs : inp list, i j : int) :
  total_ordering xs =>
  0 <= i < len => 0 <= j < len =>
  rel xs i j => rel xs j i => i = j.
proof. rewrite /total_ordering /#. qed.

lemma total_ordering_total (xs : inp list, i j : int) :
  total_ordering xs =>
  0 <= i < len => 0 <= j < len =>
  rel xs i j \/ rel xs j i.
proof. rewrite /total_ordering /#. qed.

lemma total_ordering_ne_not_sym (xs : inp list, i j : int) :
  total_ordering xs =>
  0 <= i < len => 0 <= j < len => i <> j =>
  rel xs i j => ! rel xs j i.
proof. rewrite /total_ordering /#. qed.

type aux = unit.  (* no auxiliary information *)

(* our good lists are total orderings (aux is ignored) *)

op good (aux : aux, xs : inp list) : bool =
  total_ordering xs.

op elems_in_range (ms : int list, n : int) : bool =
  forall (i : int),
  0 <= i < size ms => 0 <= nth witness ms i < n.

lemma elems_in_range0 (n : int) :
  elems_in_range [] n.
proof. smt(). qed.

lemma elems_in_range1 (m n : int) :
  0 <= m < n => elems_in_range [m] n.
proof. rewrite /elems_in_range /#. qed.

lemma elems_in_range_cons (m : int, ms : int list, n : int) :
  elems_in_range (m :: ms) n <=>
  0 <= m < n /\ elems_in_range ms n.
proof.
rewrite /elems_in_range.
smt(size_ge0).
qed.

lemma elems_in_range_incr (ms : int list, n : int) :
  elems_in_range ms n => elems_in_range ms (n + 1).
proof. smt(). qed.

op nodups (xs : 'a list) : bool =  (* like uniq but using nth *)
  forall (i j : int),
  0 <= i < j < size xs => nth witness xs i <> nth witness xs j.

lemma nodups0 :
  nodups <:'a>[].
proof. smt(). qed.

lemma nodups_cons_def (x : 'a, ys : 'a list) :
  nodups (x :: ys) <=>
  nodups ys /\
  (forall (i : int), 0 <= i < size ys => nth witness ys i <> x).
  proof.
  split. rewrite /nodups. progress. have H4: (if i+1 = 0 then x else nth witness ys (i+1-1 )) <>
    if j+1 = 0 then x else nth witness ys (j+1 - 1).  auto. smt(). smt(). smt().
  rewrite /nodups. progress. smt(). 
(* rewrite /nodups /#. *)
qed.

(* tests whether xs is a permutation of the elements 0 ... n - 1: *)

op is_perm (n : int, xs : int list) : bool =
  size xs = n /\ elems_in_range xs n /\ nodups xs.

lemma perm_has_all (n : int, xs : int list, i : int) :
  is_perm n xs => 0 <= i < n =>
  exists (j : int), 0 <= j < n /\ nth witness xs j = i.
proof.  
have H :
  forall (n : int),
  0 <= n =>
  forall (xs : int list),
  is_perm n xs =>
  (forall (i : int),
   0 <= i < n =>
   exists (j : int), 0 <= j < n /\ nth witness xs j = i).
  clear n xs i.
  elim => [xs _ i [ge0_i lt0_i] | n ge0_n IH xs].
  have // : 0 < 0 by rewrite (ler_lt_trans i).
  rewrite /is_perm /elems_in_range =>
    [[#] size_xs all_xs_in_rng no_dups_xs i [ge0_i lt_i_n_plus1]].
  rewrite size_xs in all_xs_in_rng.
  case (exists j, 0 <= j < n + 1 /\ nth witness xs j = n) =>
    [[j [#] ge0_j lt_j_n_plus1 jth_xs_eq_n] | all_xs_ne_n].
  case (i = n) => [eq_i_n | ne_i_n].
  exists j; smt().
  have [k [#] ge0_k lt_k_n <-] := IH (trim xs j) _ i _.
    rewrite /is_perm /elems_in_range /=.
    split; first smt(size_trim).
    rewrite /trim.
    smt(nth_cat size_cat size_take size_drop nth_take nth_drop).
    smt().
  rewrite /trim nth_cat size_take // size_xs lt_j_n_plus1 /=.
  case (k < j) => [lt_k_j | not_lt_k_j].
  exists k; smt(nth_take).
  exists (k + 1); smt(nth_drop).
  rewrite negb_exists /= in all_xs_ne_n.
  have ge0_hd_xs_lt_n : 0 <= head witness xs < n by smt(nth0_head).
  have [j [#] ge0_j lt_j_n jth_behead_xs_eq_head_xs]
         := IH (behead xs) _ (head witness xs) _.
    rewrite /is_perm /nodups.
    smt(nth_behead head_behead).
    trivial.
  have /# :  (* contradiction *)
       exists (i j : int),
       0 <= i < j < n + 1 /\ nth witness xs i = nth witness xs j.
    exists 0 (j + 1); smt(nth0_head nth_behead).
move => is_perm_gne_n_xs [ge0_i lt_i_n].
by rewrite H 1:(ler_trans i) // ltrW.
qed.

(* tests whether xs is a permutation of the elements 0 ... len - 1: *)

op is_perm_len : int list -> bool = is_perm len.

lemma perm_len_has_all (xs : int list, i : int) :
  is_perm_len xs => 0 <= i < len =>
  exists (j : int), 0 <= j < len /\ nth witness xs j = i.
proof. apply perm_has_all. qed.

(* assuming total_ordering xs and elems_in_range ms len: *)

op sorted (xs : inp list, ms : int list) : bool =
  forall (i j : int),
  0 <= i <= j < size ms =>
  rel xs (nth witness ms i) (nth witness ms j).

lemma sorted0 (xs : inp list) :
  sorted xs [].
proof. smt(). qed.

lemma sorted1 (xs : inp list, m : int) :
  total_ordering xs => 0 <= m < len => sorted xs [m].
proof.
move => tot_ord_xs [ge0 lt_m_len].
rewrite /sorted.
smt(total_ordering_refl).
qed.

lemma sorted_cons_def (xs : inp list, m : int, ms : int list) :
  total_ordering xs =>
  sorted xs (m :: ms) /\ elems_in_range (m :: ms) len <=>
  (ms = [] /\ 0 <= m < len \/
   ms <> [] /\ 0 <= m < len /\ rel xs m (head witness ms) /\
   sorted xs ms /\ elems_in_range ms len).
proof.
move => tot_ord_xs.
split =>
  [[srtd_m_ms eir_m_ms] |
   [[#] -> ge0_m lt_m_len |
    [#] ge0_m lt_m_len ms_nonnil rel_xs_m_hd_ms srtd_xs_ms eir_ms]].
case (ms = []) => [_ /= | /= ms_nonnil].
smt(elems_in_range_cons).
split; first smt(elems_in_range_cons).
split.
have -> : m = nth witness (m :: ms) 0 by smt().
have -> : head witness ms = nth witness (m :: ms) 1.
  by rewrite /= nth0_head.
rewrite srtd_m_ms /=.
smt(size_ge0 size_eq0).
split => [i j [#] ge0_i le_i_j lt_j_size_ms |].
have -> : nth witness ms i = nth witness (m :: ms) (i + 1) by smt().
have -> : nth witness ms j = nth witness (m :: ms) (j + 1) by smt().
rewrite srtd_m_ms /#.
smt(elems_in_range_cons).
by rewrite sorted1 //= elems_in_range1.
split.
move => i j [#] /= ge0_i le_i_j lt_j_size_ms_plus1.
case (i = 0) => [eq0_i | ne0_i].
case (j = 0) => [eq0_j | ne0_j].
by rewrite total_ordering_refl.
rewrite (total_ordering_trans xs (head witness ms)) //.
smt(nth0_head).
smt().
smt(nth0_head).
smt().
smt(elems_in_range_cons).
qed.

lemma sorted_cons_nonempty (xs : inp list, m : int, ms : int list) :
  total_ordering xs => 0 <= m < len => ms <> [] =>
  elems_in_range ms len => rel xs m (head witness ms) => sorted xs ms =>
  sorted xs (m :: ms).
proof. smt(sorted_cons_def). qed.

lemma sorted_cons_nonempty_rel (xs : inp list, m : int, ms : int list) :
  ms <> [] => sorted xs (m :: ms) =>
  rel xs m (head witness ms).
proof.
move => ms_nonnil srtd_m_ms.
have -> : m = nth witness (m :: ms) 0 by smt().
have -> : head witness ms = nth witness (m :: ms) 1.
  by rewrite /= nth0_head.
rewrite srtd_m_ms /=.
smt(size_ge0 size_eq0).
qed.

op insert_in_sorted (xs : inp list, n : int, ms : int list) : int list =
  with ms = []      => [n]
  with ms = l :: ls =>
    if rel xs n l
    then n :: ms
    else l :: insert_in_sorted xs n ls.

lemma insert_in_sorted_size (xs : inp list, n : int, ms : int list) :
  size (insert_in_sorted xs n ms) = size ms + 1.
proof. elim ms; smt(). qed.

lemma insert_in_sorted_nonnil (xs : inp list, n : int, ms : int list) :
  insert_in_sorted xs n ms <> [].
proof. smt(insert_in_sorted_size size_eq0). qed.

lemma insert_in_sorted_head (xs : inp list, n : int, ms : int list) :
  ms <> [] /\
  head witness (insert_in_sorted xs n ms) = head witness ms \/
  head witness (insert_in_sorted xs n ms) = n.
proof.
case ms => [// | m ms /=].
by case (rel xs n m).
qed.

lemma insert_in_sorted_elems_in_range_gen
      (len' : int, xs : inp list, n : int, ms : int list) :
  1 <= len' => total_ordering xs =>
  0 <= n < len' => elems_in_range ms len' =>
  elems_in_range (insert_in_sorted xs n ms) len'.
proof.
move => ge1_len' tot_ord_xs [ge0_n lt_n_len'].
elim ms => [/= | l ls IH /= eir_ls].
rewrite /elems_in_range /#.
case (rel xs n l) => [rel_xs_n_l | not_rel_xs_n_l].
by rewrite elems_in_range_cons.
rewrite elems_in_range_cons.
split; first smt(elems_in_range_cons).
rewrite IH.
smt(elems_in_range_cons).
qed.

lemma insert_in_sorted_elems_in_range
      (xs : inp list, n : int, ms : int list) :
  total_ordering xs => 0 <= n < len => elems_in_range ms len =>
  elems_in_range (insert_in_sorted xs n ms) len.
proof.
apply insert_in_sorted_elems_in_range_gen.
rewrite ge1_len.
qed.

op all_nth_ne (l : 'a, ms : 'a list) : bool =
  forall (i : int),
  0 <= i < size ms => nth witness ms i <> l.

lemma insert_in_sorted_not_elem_nth
      (xs : inp list, k n : int, ms : int list) :
  total_ordering xs => k <> n => all_nth_ne k ms =>
  all_nth_ne k (insert_in_sorted xs n ms).
proof.
move => tot_ord_xs ne_k_n.
rewrite /all_nth_ne.
elim ms => [/# | l ls IH k_not_in_l_ls i].
rewrite insert_in_sorted_size /= => [[ge0_i lt_i_size_ls_plus2]]. 
case (rel xs n l) => [rel_xs_n_l | not_rel_xs_n_l].
case (i = 0) => [/# | ne0_i].
case (i - 1 = 0) => [eq0_i_min1 | ne0_i_min1].
have -> : l = nth witness (l :: ls) 0 by smt().
rewrite k_not_in_l_ls /=; smt(size_ge0).
have -> :
  nth witness ls (i - 1 - 1) = nth witness (l :: ls) (i - 1)
  by smt().
rewrite k_not_in_l_ls /=; smt(size_ge0).
case (i = 0) => [eq0_i | ne0_i].
have -> : l = nth witness (l :: ls) 0 by smt().
rewrite k_not_in_l_ls /=; smt(size_ge0).
apply IH.
move => j [ge0_j lt_j_size_ls].
have -> : nth witness ls j = nth witness (l :: ls) (j + 1) by smt().
rewrite k_not_in_l_ls //=; smt(size_ge0).
rewrite insert_in_sorted_size; smt(size_ge0).
qed.

lemma insert_in_sorted_no_dups (xs : inp list, n : int, ms : int list) :
  total_ordering xs => all_nth_ne n ms =>  
  nodups ms => nodups (insert_in_sorted xs n ms).
proof.
move => tot_ord_xs.
elim ms => [/= _ | l ls IH n_not_in_l_ls nodups_l_ls /=].
smt().
case (rel xs n l) => [rel_xs_n_l | not_rel_xs_n_l].
rewrite nodups_cons_def.
split; first rewrite nodups_l_ls.
move => i [ge0_i lt_i_size_l_ls].
by rewrite n_not_in_l_ls.
rewrite nodups_cons_def.
split.
rewrite IH => [i [ge0_i lt_i_size_ls] |].
have -> : nth witness ls i = nth witness (l :: ls) (i + 1) by smt().
rewrite n_not_in_l_ls /#.
smt(nodups_cons_def).
apply insert_in_sorted_not_elem_nth => //.
have -> : l = nth witness (l :: ls) 0 by smt().
rewrite n_not_in_l_ls //=; smt(size_ge0).
smt(nodups_cons_def).
qed.

lemma insert_in_sorted_perm_gen (xs : inp list, n : int, ms : int list) :
  total_ordering xs => 0 <= n < len => is_perm n ms =>
  is_perm (n + 1) (insert_in_sorted xs n ms).
proof.
move => tot_ord_xs [ge0_n lt_n_len].
rewrite /is_perm => [#] size_ms_eq_n eir_ms_n no_dups_ms.
split; first rewrite insert_in_sorted_size /#.
split.
by rewrite insert_in_sorted_elems_in_range_gen // 1:/# 1:/#
           elems_in_range_incr.
rewrite insert_in_sorted_no_dups // /#.
qed.

lemma insert_in_sorted_sorted (xs : inp list, n : int, ms : int list) :
  total_ordering xs => 0 <= n < len => elems_in_range ms len =>
  sorted xs ms => sorted xs (insert_in_sorted xs n ms).
proof.
move => tot_ord_xs.
elim ms =>
  [[ge0_n lt_n_len] _ _ /= |
   m ms IH lt_n_len range_m_ms sorted_m_ms /=].
by rewrite sorted1.
case (rel xs n m) => [rel_xs_n_m | not_rel_xs_n_m].
smt(sorted_cons_def).
have ge0_m_lt_len : 0 <= m < len.
  have -> : m = nth witness (m :: ms) 0 by trivial.
  rewrite range_m_ms /=; smt(size_ge0).
rewrite sorted_cons_nonempty //.
by rewrite insert_in_sorted_nonnil.
rewrite insert_in_sorted_elems_in_range //.
smt(elems_in_range_cons).
have [[ms_ne_nil ->] | ->] := insert_in_sorted_head xs n ms.
by rewrite sorted_cons_nonempty_rel.
smt(total_ordering_total).
rewrite IH //.
smt(elems_in_range_cons).
smt(sorted_cons_def).
qed.

lemma sorted_perm_exists (xs : inp list) :
  total_ordering xs =>
  exists (perm : int list),
  is_perm_len perm /\ sorted xs perm.
proof.
move => tot_ord_xs.
have H :
  forall (n : int),
  0 <= n => n <= len =>
  exists (perm : int list),
  is_perm n perm /\ elems_in_range perm len /\ sorted xs perm.
  elim => [_ | n ge0_n IH le_n_len].
  exists []; smt().
  have lt_n_len: n < len by smt().
  have [perm [#] ip_n_perm eir_perm_len srtd_xs_perm] := IH _.
    smt().
  exists (insert_in_sorted xs n perm).
  split; first by rewrite insert_in_sorted_perm_gen.
  split; first by rewrite insert_in_sorted_elems_in_range.
  by rewrite insert_in_sorted_sorted.
have /# := H len _ _.
  rewrite (ler_trans 1) // ge1_len.
  trivial.
qed.

lemma diff_equal_size_least_index_diff (xs ys : 'a list) :
  xs <> ys => size xs = size ys => 
  (exists (i : int),
   0 <= i < size xs /\ nth witness xs i <> nth witness ys i /\
   (forall (j : int),
    0 <= j < i => nth witness xs j = nth witness ys j)).
proof.
move => eq_size ne_xs_ys.
pose P :=
  fun (i : int) =>
  i < size xs /\ nth witness xs i <> nth witness ys i.
have /# := pmin_spec P _.
  rewrite /sempty /pcap /P negb_forall /=.
  case
    (exists i,
     0 <= i < size xs /\
     nth witness xs i <> nth witness ys i) => [/# |].
  rewrite negb_exists /= => H.
  have // := eq_from_nth witness xs ys _ _.
    trivial. smt().
qed.

lemma sorted_perm_uniq (xs : inp list, perm1 perm2 : int list) :
  total_ordering xs =>
  is_perm_len perm1 => is_perm_len perm2 =>
  sorted xs perm1 => sorted xs perm2 =>
  perm1 = perm2.
proof.
move => tot_ord_xs is1 is2 srted1 srted2.
case (perm1 = perm2) => [// | ne_perms].
have [i [#] ge0_i lt_i_size nth_ne_at_i min_prop]
       := diff_equal_size_least_index_diff perm1 perm2 _ _.
  smt(). smt().
have [k1 [#] lt_i_k1 lt_k1_size perm1_at_k1_eq_perm2_at_i] :
  exists (k1 : int),
  i < k1 < size perm1 /\ nth witness perm1 k1 = nth witness perm2 i.
  have [j [#] ge0_j lt_j_len perm1_at_j_eq_perm2_at_i]
         := perm_len_has_all perm1 (nth witness perm2 i) _ _.
    trivial. smt().
  have i_lt_j_lt_len : i < j by smt().
  exists j; smt().
have [k2 [#] lt_i_k2 lt_k2_size perm2_at_k2_eq_perm1_at_i] :
  exists (k2 : int),
  i < k2 < size perm1 /\ nth witness perm2 k2 = nth witness perm1 i.
  have [j [#] ge0_j lt_j_len perm2_at_j_eq_perm1_at_i]
         := perm_len_has_all perm2 (nth witness perm1 i) _ _.
    trivial. smt().
  have i_lt_j_lt_len : i < j by smt().
  exists j; smt().
have rel_i_12 : rel xs (nth witness perm1 i) (nth witness perm2 i).
  smt().
have rel_i_21 : rel xs (nth witness perm2 i) (nth witness perm1 i).
  smt().
smt(total_ordering_ne_not_sym).
qed.

op sorted_perm_len_rel (xs : inp list, perm : int list) : bool =
  is_perm_len perm /\ sorted xs perm.

lemma sorted_perm_rel_exists (xs : inp list) :
  total_ordering xs =>
  exists (perm : int list), sorted_perm_len_rel xs perm.
proof. apply sorted_perm_exists. qed.

lemma sorted_perm_len_rel_uniq (xs : inp list, perm1 perm2 : int list) :
  total_ordering xs =>
  sorted_perm_len_rel xs perm1 => sorted_perm_len_rel xs perm2 =>
  perm1 = perm2.
proof.
move => tot_ord_xs [ispl1 srted1] [ispl2 srted2].
by rewrite (sorted_perm_uniq xs perm1 perm2).
qed.

(* now we can define our f and show it has the correct property *)

type out = int list.

op f (aux : aux, xs : inp list) : out option =
  if total_ordering xs
  then Some (choiceb (sorted_perm_len_rel xs) [])
  else None.

lemma f_prop (xs : inp list) :
  total_ordering xs =>
  is_some (f () xs) /\ is_perm_len (oget (f () xs)) /\
  sorted xs (oget (f () xs)).
proof.
move => tot_ord_xs.
have := choicebP (sorted_perm_len_rel xs) [] _.
  by rewrite sorted_perm_rel_exists.
by rewrite /f /sorted_perm_len_rel tot_ord_xs.
qed.

lemma f_is_some (xs : inp list) :
  total_ordering xs => is_some (f () xs).
proof.
move => tot_ord_xs.
smt(f_prop).
qed.

lemma f_is_perm_len (xs : inp list) :
  total_ordering xs => is_perm_len (oget (f () xs)).
proof.
move => tot_ord_xs.
smt(f_prop).
qed.

lemma f_sorted (xs : inp list) :
  total_ordering xs => sorted xs (oget (f () xs)).
proof.
move => tot_ord_xs.
smt(f_prop).
qed.

lemma f_bad (xs : inp list) :
  ! total_ordering xs => f () xs = None.
proof. smt(). qed.

clone import AdvLowerBounds as ALB with
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
  elim H.
  rewrite /total_ordering !negb_and => -> //.
  elim.
  have // : all (mem univ) xs by smt(allP).
  by rewrite /good.
smt(f_bad).
(* end of realization *)
