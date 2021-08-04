(* Problem Specification for Searching in Ordered Lists *)

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
   that the list has k at that position; it can query the values of
   elements of the list

   these definitions are used for both the upper bound proof for the
   binary search algorithm, and the lower bound proof for the
   searching problem *)

require import AllCore List FSetAux StdOrder IntDiv.
import IntOrder.

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

lemma in_univ (inp : inp) :
  inp \in univ <=> min_inp <= inp /\ inp <= max_inp.
proof. smt(mem_range). qed.

lemma min_inp_univ :
  min_inp \in univ.
proof.
smt(in_univ lt_min_max).
qed.

lemma max_inp_univ :
  max_inp \in univ.
proof.
smt(in_univ lt_min_max).
qed.

type out = int.

(* arity can be any positive number (otherwise int_log_up 2 arity would
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
