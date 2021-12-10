(* Generating All Lists of Length Over Universe *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020-2021 - Boston University
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

prover [""].  (* no use of SMT provers *)

require import AllCore List FSetAux.

lemma all_flatten (f : 'a -> bool, xss : 'a list list) :
  all f (flatten xss) = all (all f) xss.
proof.
elim xss => [| x xss IH /=].
by rewrite flatten_nil.
by rewrite flatten_cons all_cat IH.
qed.

op nosmt next (xs : 'a list, yss : 'a list list) : 'a list list =
  flatten
  (map
   (fun x =>
      map (fun ys => x :: ys) yss)
   xs).

lemma next (xs : 'a list, yss : 'a list list) :
  next xs yss =
  flatten
  (map
   (fun x =>
      map (fun ys => x :: ys) yss)
   xs).
proof.
by rewrite /next.
qed.

lemma next_uniq (xs : 'a list, yss : 'a list list) :
  uniq xs => uniq yss => uniq (next xs yss).
proof.
move => uniq_xs uniq_yss.
rewrite next uniq_flatten_map //=.
move => x; by rewrite map_inj_in_uniq.
move => u v u_in_xs v_in_xs.
rewrite hasP => [[zs []]].
rewrite mapP => [[us [_ ->]]].
rewrite mapP => [[vs [_ //]]].
qed.

lemma sumz_nseq (n m : int) :
  0 <= n => sumz (nseq n m) = n * m.
proof.
rewrite /sumz.
elim n => [| i ge0_i IH].
by rewrite nseq0.
by rewrite nseqS //= IH mulrDl /= addrC.
qed.

lemma next_size (xs : 'a list, yss : 'a list list) :
  size (next xs yss) = size xs * size yss.
proof.
rewrite next size_flatten /=.
have -> :
  map size (map (fun (x : 'a) => map ((::) x) yss) xs) =
  nseq (size xs) (size yss).
elim xs => [/= | x xs IH /=].
by rewrite nseq0.
by rewrite addrC nseqS 1:size_ge0 IH /= size_map.
by rewrite sumz_nseq 1:size_ge0.
qed.

op all_lists (xs : 'a list, n : int) = fold (next xs) [[]] n.

lemma all_lists0 (xs : 'a list) :
  all_lists xs 0 = [[]].
proof.
by rewrite /all_lists fold0.
qed.

lemma all_listsS (xs : 'a list, n : int) :
  0 <= n =>
  all_lists xs (n + 1) = next xs (all_lists xs n).
proof.
move => ge0_n.
by rewrite /all_lists foldS.
qed.

lemma all_list_uniq (xs : 'a list, n : int) :
  uniq xs => 0 <= n => uniq (all_lists xs n).
proof.
move => uniq_xs; move : n.
elim => [| i ge0_i uniq_al_xs_i].
by rewrite all_lists0.
by rewrite all_listsS // next_uniq.
qed.

lemma all_lists_size (xs : 'a list, n : int) :
  0 <= n => size (all_lists xs n) = size xs ^ n.
proof.
elim n => [| i ge0_i IH].
by rewrite all_lists0 /= expr0.
by rewrite all_listsS // next_size IH exprS.
qed.

lemma all_listsS_iff (xs ys : 'a list, n : int) :
  0 <= n =>
  ys \in all_lists xs (n + 1) <=>
  exists (z : 'a, zs : 'a list),
  ys = z :: zs /\ z \in xs /\ zs \in all_lists xs n.
proof.
move => ge0_n.
rewrite all_listsS // next /= -flatten_mapP.
split => [[z] [#] /= |].
rewrite mapP => z_in_xs [zs] [#] => zs_in_all_n ->>.
by exists z zs.
move => [z zs] [#] -> z_in_xs zs_in_all_n.
exists z.
by rewrite z_in_xs /= (map_f ((::) z)).
qed.

lemma all_lists_arity_wanted (xs : 'a list, n : int) :
  0 <= n =>
  all
  (fun ys => size ys = n /\ all (mem xs) ys)
  (all_lists xs n).
proof.
elim n => [| i ge0_i IH].
by rewrite all_lists0.
rewrite allP in IH.
rewrite allP => zs.
rewrite all_listsS_iff //.
move => [w ws] [#] -> w_in_xs ws_in_all_i /=.
rewrite w_in_xs /=.
have /= [#] <- -> /= := (IH ws ws_in_all_i).
by rewrite addzC.
qed.

lemma all_lists_arity_have (xs ys : 'a list, n : int) :
  0 <= n => size ys = n => (all (mem xs) ys) =>
  ys \in all_lists xs n.
proof.
move : n.
elim ys => [n ge0_n /= <- | y ys IH n ge0_n].
by rewrite all_lists0.
rewrite /= => <- [#] y_in_xs all_mem_xs_ys.
rewrite addzC all_listsS_iff 1:size_ge0.
exists y ys => /=.
by rewrite y_in_xs /= IH 1:size_ge0.
qed.

lemma size_nseq_norm (n : int, x : 'a) :
  0 <= n => size (nseq n x) = n.
proof.
rewrite lez_eqVlt => ge0_n.
rewrite size_nseq /max.
by elim ge0_n => ->.
qed.

lemma all_lists_nseq (x : 'a, xs : 'a list, n : int) :
  0 <= n => x \in xs => nseq n x \in all_lists xs n.
proof.
move => ge0_n x_in_xs.
rewrite all_lists_arity_have //.
by rewrite size_nseq_norm.
rewrite allP => z; by rewrite mem_nseq => [#] _ => ->>.
qed.

(* makes a list of length n all of whose elements are either
   x1 or x2; when the elements index i is in zs, x1 is used;
   otherwise x2 is used *)

op make_list_either (x1 x2 : 'a, f : int -> bool, n : int) : 'a list =
  mkseq (fun i => if f i then x1 else x2) n.

lemma make_list_either_size (x1 x2 : 'a, f : int -> bool, n : int) :
  0 <= n => size (make_list_either x1 x2 f n) = n.
proof.
rewrite lez_eqVlt => ge0_n.
rewrite /make_list_either size_mkseq /max.
by elim ge0_n => ->.
qed.

lemma make_list_either_all_in
      (xs : 'a list, x1 x2 : 'a, f : int -> bool, n : int) :
  0 <= n => x1 \in xs => x2 \in xs =>
  all (mem xs) (make_list_either x1 x2 f n).
proof.
move => ge0_n x1_in_xs x2_in_xs.
rewrite /make_list_either allP => z.
rewrite mkseqP => [] [i] [#] ge0_i i_rng -> /=.
by case (f i).
qed.

lemma make_list_either_in_all_lists
      (xs : 'a list, x1 x2 : 'a, f : int -> bool, n : int) :
  0 <= n => x1 \in xs => x2 \in xs =>
  (make_list_either x1 x2 f n) \in all_lists xs n.
proof.
move => ge0_n x1_in_xs x2_in_xs.
by rewrite all_lists_arity_have // 1:make_list_either_size //
           make_list_either_all_in.
qed.

lemma make_list_either_nth (x1 x2 : 'a, f : int -> bool, n, i : int) :
  0 <= n => 0 <= i < n =>
  nth witness (make_list_either x1 x2 f n) i = if f i then x1 else x2.
proof.
move => ge0_n i_rng.
rewrite /make_list_either.
by rewrite nth_mkseq.
qed.
