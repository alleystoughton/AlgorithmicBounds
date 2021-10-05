(* Auxiliary Lemmas on Finite Sets *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020-2021 - Boston University
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

prover [""].  (* no use of SMT provers *)

require import AllCore List.
require export FSet.

lemma fcardUindep1 (xs : 'a fset, x : 'a) :
  ! x \in xs => card (xs `|` fset1 x) = card xs + 1.
proof.
move => x_notin_xs.
by rewrite fcardUI_indep 1:fsetI1 1:x_notin_xs // fcard1.
qed.

lemma all_elemsP (f : 'a -> bool, xs : 'a fset) :
  all f (elems xs) <=> (forall (x : 'a), x \in xs => f x).
proof.
rewrite allP.
split => [H x x_in_xs | H x x_in_elems_xs].
by rewrite H -memE.
by rewrite H memE.
qed.

lemma all_elems_or (f : 'a -> bool, xs ys : 'a fset) :
  all f (elems (xs `|` ys)) <=> (all f (elems xs) /\ all f (elems ys)).
proof.
rewrite !all_elemsP.
split => [H | [#] H1 H2].
split => [z z_in_xs | z z_in_ys].
rewrite H in_fsetU; by left.
rewrite H in_fsetU; by right.
move => z; rewrite in_fsetU => [[z_in_xs | z_in_ys]].
by rewrite H1.
by rewrite H2.
qed.

lemma fset1_ne_fset0 (x : 'a) :
  fset1 x <> fset0.
proof.
case (fset1 x = fset0) => [H /= | //].
by rewrite -(in_fset0 x) -H in_fset1.
qed.

lemma union_eq_fset0_iff (xs ys : 'a fset) :
  xs `|` ys = fset0 <=> xs = fset0 /\ ys = fset0.
proof.
split => [xs_union_ys_eq_fset0 | [-> ->]].
split.
rewrite fsetP => x.
split => [x_in_xs |].
rewrite -xs_union_ys_eq_fset0 in_fsetU.
by left.
by rewrite in_fset0.
rewrite fsetP => x.
split => [x_in_xs |].
rewrite -xs_union_ys_eq_fset0 in_fsetU.
by right.
by rewrite in_fset0.
by rewrite fsetU0.
qed.

lemma fset1_union_any_ne_fset0 (x : 'a, xs : 'a fset) :
  fset1 x `|` xs <> fset0.
proof.
rewrite union_eq_fset0_iff negb_and.
left.
case (fset1 x = fset0) => [H | //].
by rewrite /= -(in_fset0 x) -H in_fset1.
qed.

lemma oflist_eq_fset0_iff (xs : 'a list) :
  oflist xs = fset0 <=> xs = [].
proof.
case xs => [/= | x xs /=].
by rewrite -set0E.
by rewrite oflist_cons fset1_union_any_ne_fset0.
qed.

lemma uniq_card_oflist (xs : 'a list) :
  uniq xs => card (oflist xs) = size xs.
proof.
move => uniq_xs.
rewrite cardE (perm_eq_size (elems (oflist xs)) xs) //.
by rewrite perm_eq_sym oflist_uniq.
qed.
