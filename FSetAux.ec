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

lemma disjointP (xs ys : 'a fset) :
  xs `&` ys = fset0 <=> forall (x : 'a), x \in xs => ! x \in ys.
proof.
split => [disj_xs_ys x x_in_xs | all_xs_not_in_ys].
case (x \in ys) => [x_in_ys | //].
have x_in_inter_xs_ys : x \in (xs `&` ys) by rewrite in_fsetI.
have // : false by rewrite -(in_fset0 x) -disj_xs_ys.
rewrite fsetP => x.
rewrite in_fsetI in_fset0 /= negb_and.
case (x \in xs) => [x_in_xs | //].
right; by rewrite all_xs_not_in_ys.
qed.
