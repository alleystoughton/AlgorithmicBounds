(* Showing Uniq Lists Have Same Size Via Existence of Injective
   Surjection *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2021-2022 - Boston University
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

prover quorum=2 ["Alt-Ergo" "Z3"].

timeout 2.  (* can increase *)

require import AllCore List.

(* f is a function from xs to ys *)

op lists_fun (xs : 'a list, ys : 'b list, f : 'a -> 'b) : bool =
  forall (x : 'a), x \in xs => f x \in ys.

(* f is an injective function from xs to ys; should only be used when
   lists_fun xs ys f *)

op lists_fun_injective
   (xs : 'a list, ys : 'b list, f : 'a -> 'b) : bool =
  (forall (x, x' : 'a),
   x \in xs => x' \in xs => f x = f x' => x = x').

(* f is a surjective function from xs to ys; should only be used when
   lists_fun xs ys f *)

op lists_fun_surjective
   (xs : 'a list, ys : 'b list, f : 'a -> 'b) : bool =
  (forall (y : 'b),
   y \in ys => exists (x : 'a), x \in xs /\ f x = y).

lemma uniq_sets_eq_size_if_injective_surjective
      (xs : 'a list, ys : 'b list, f : 'a -> 'b) :
  uniq xs => uniq ys => lists_fun xs ys f =>
  lists_fun_injective xs ys f => lists_fun_surjective xs ys f =>
  size xs = size ys.
proof.
move : xs ys.
elim =>
  [/= ys uniq_ys _ _ lfs_nil_ys_f |
   u vs IH ys [not_u_in_vs uniq_vs] uniq_ys lf_u_cons_vs_ys_f
   lfi_u_cons_vs_ys_f lfs_u_cons_vs_ys_f /=].
case (ys = []) => [/# | ne_nil_ys].
have := head_behead ys witness _ => //#.
pose y := f u.
have y_in_ys : y \in ys by smt().
have := splitPr ys y _ => // [[ys1 ys2] ys_eq].
have y_not_in_ys1_cat_ys2 : ! y \in ys1 ++ ys2.
  rewrite mem_cat negb_or.
  have := cat_uniq ys1 (y :: ys2).
  smt().
have lf_vs_ys1_cat_ys2_f : lists_fun vs (ys1 ++ ys2) f.
  move => x x_in_xs.
  have : f x \in ys by smt().
  rewrite ys_eq.
  rewrite mem_cat /= => [[| [f_x_eq_y |]]].
  smt(mem_cat).
  smt(cat_uniq).  (* by contradiction *)
  smt(mem_cat).
have lfi_vs_ys1_cat_ys2 : lists_fun_injective vs (ys1 ++ ys2) f.
  move => a a' a_in_vs a'_in_vs f_a_eq_f_a'.
  apply lfi_u_cons_vs_ys_f => //#.
have lfs_vs_ys1_cat_ys2 : lists_fun_surjective vs (ys1 ++ ys2) f.
  move => b b_in_ys.
  have [x /= [x_in_u_vs f_x_eq_b]] := lfs_u_cons_vs_ys_f b _.
    smt(cat_uniq mem_cat).
  elim x_in_u_vs => [eq_x_u | x_in_vs].
  have f_u_eq_b : f u = b by rewrite -eq_x_u.
  smt().  (* by contradiction *)
  by exists x.
rewrite ys_eq size_cat /= (addrC (size ys1)) -addrA.
congr.
rewrite addrC -size_cat.
rewrite (IH (ys1 ++ ys2)) //.
rewrite cat_uniq.
have /# := cat_uniq ys1 (y :: ys2).
qed.
