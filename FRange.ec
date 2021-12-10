(* Theory of Finite Ranges as Sets *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020-2021 - Boston University
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

prover [""].  (* no use of SMT provers *)

require import AllCore List FSetAux.

(* frange n is {i | 0 <= i < n} *)

op frange (n : int) : int fset = oflist (range 0 n).

(* let's prove this definition is good: *)

lemma frange_impl_range (n i : int) :
  i \in frange n => 0 <= i < n.
proof.
by rewrite mem_oflist mem_range.
qed.

lemma range_impl_frange (n i : int) :
  0 <= i < n => i \in frange n.
proof.
by rewrite mem_oflist mem_range.
qed.

lemma frange_iff_range (n i : int) :
  i \in frange n <=> 0 <= i < n.
proof.
split; [apply frange_impl_range | apply range_impl_frange].
qed.

lemma frange0 :
  frange 0 = fset0.
proof.
by rewrite /frange range_geq // -set0E.
qed.

lemma frangeS (n : int) :
  0 <= n => frange (n + 1) = frange n `|` fset1 n.
proof.
move => ge0_n.
rewrite fsetP => i.
rewrite in_fsetU1 2!mem_oflist 2!mem_range.
split => [[#] ge0_i i_lt_n_plus1 | [[#] ge0_i lt_i_n | ->]].
rewrite ltzS lez_eqVlt in i_lt_n_plus1.
elim i_lt_n_plus1 => [// | i_lt_n]; by left.
split => [// | _]; rewrite ltzS lez_eqVlt; by right.
split => [// |]; by rewrite ltzS lezz.
qed.

lemma card_frange (n : int) :
  0 <= n => card (frange n) = n.
proof.
elim n => [| i ge0_i IH].
by rewrite frange0 fcards0.
rewrite frangeS // fcardUindep1.
case (i \in frange i) => [| //].
by rewrite frange_iff_range.
by rewrite IH.
qed.

lemma sub_range_card_leq (xs : int fset, n : int) :
  0 <= n =>
  (forall (j : int), j \in xs => 0 <= j < n) =>
  card xs <= n.
proof.
move => ge0_n xs_sub_range.
rewrite -card_frange // subset_leq_fcard => i i_in_xs.
by rewrite range_impl_frange xs_sub_range.
qed.

lemma all_range_card_geq (xs : int fset, n : int) :
  0 <= n =>
  (forall (j : int), 0 <= j < n => j \in xs) =>
  n <= card xs.
proof.
move => ge0_n sub_xs.
rewrite -card_frange //.
rewrite subset_leq_fcard => i i_in_frange.
by rewrite sub_xs frange_impl_range.
qed.

lemma sub_range_card_max (xs : int fset, n : int) :
  card xs = n =>
  (forall (j : int), j \in xs => 0 <= j < n) =>
  (forall (j : int), 0 <= j < n => j \in xs).
proof.
move => <<- xs_sub_range j zero_le_j_lt_card_xs.
have -> : xs = frange (card xs).
  rewrite eqEcard.
  split => [i i_in_xs |].
  by rewrite range_impl_frange xs_sub_range.
  rewrite card_frange 1:fcard_ge0 lezz.
by rewrite range_impl_frange.
qed.
