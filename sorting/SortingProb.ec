(* Problem Specification for Comparison-based Sorting of Lists *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2021-2022 - Boston University
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
   questions about the values of the list elements themselves

   formally, the algorithm is trying to figure out how the list 0
   .. len - 1 should be permuted so as to be sorted according to a
   given total ordering

   but this is equivalent to figuring out how a list of distinct
   elements of size len should be permuted so as to be sorted
   according to some total ordering

   this is because given a list xs of distinct element of size len, we
   can go back and forth between total orderings on 0 .. len - 1 and
   total orderings on xs (if rel is a total ordering on 0 .. len - 1,
   we can make it into a total ordering rel' on xs by: a <= b iff
   the index i of a in xs is <= the index j of b in xs; if rel' is
   a total ordering on xs, we can make it into a total ordering on
   0 .. len - 1 by: i <= j iff the ith element of xs is <= the jth
   element of xs *)

require import AllCore List IntDiv StdOrder IntMin FSetAux Perms Binomial.
import IntOrder.

require Bounds.  (* bounds abstract theory *)

op len : int.  (* size of list of distinct elements *)

axiom ge1_len : 1 <= len.

lemma gt0_len : 0 < len.
proof.
rewrite (ltr_le_trans 1) // ge1_len.
qed.

lemma ge0_len : 0 <= len.
proof.
rewrite (ler_trans 1) // ge1_len.
qed.

(* to represent this problem using our lower and upper bound
   frameworks, we encode queries (i, j), for 0 <= i, j < len, as
   integers between 0 and arity - 1, for arity = len * len: *)

op arity : int = len * len.

lemma ge1_arity : 1 <= arity.
proof.
rewrite /arity mulr_ege1 ge1_len.
qed.

lemma ge0_arity : 0 <= arity.
proof.
rewrite (ler_trans 1) // ge1_arity.
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

lemma enc_bounds_ge0 (p : int * int) :
  0 <= p.`1 < len => 0 <= p.`2 < len =>
  0 <= enc p.
proof. smt(enc_bounds). qed.

lemma enc_bounds_lt_arity (p : int * int) :
  0 <= p.`1 < len => 0 <= p.`2 < len =>
  enc p < arity.
proof. smt(enc_bounds). qed.

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

(* we can represent a total ordering on the numbers between
   0 .. len - 1 as a list of booleans of size arity *)

type inp = bool.

op univ : inp list = [true; false].  (* so no restriction *)

(* assuming size xs = arity, 0 <= i < len and 0 <= j < len, rel xs i j
   tests whether i is less-than-or-equal-to j in relation xs *)

op rel (xs : inp list, i j : int) : bool =
  nth false xs (enc (i, j)).

op nosmt total_ordering (xs : inp list) : bool =
  size xs = arity /\
  (* reflexivity *)
  (forall (i : int), 0 <= i < len => rel xs i i) /\
  (* transitivity *)
  (forall (i j k : int),
   0 <= i < len => 0 <= j < len => 0 <= k < len =>
   rel xs i j => rel xs j k => rel xs i k) /\
  (* antisymmetry *)
  (forall (i j : int),
   0 <= i < len => 0 <= j < len =>
   rel xs i j => rel xs j i => i = j) /\
  (* totality *)
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

(* turn total ordering into comparison function on all of int that
   is reflexive, transitive, antisymmetric and total

   we only care what cmp_of_rel xs i j is when 0 <= i < len and 0 <= j
   < len *)

op nosmt cmp_of_rel (xs : inp list) (i j : int) : bool =
  if 0 <= i < len /\ 0 <= j < len
    then rel xs i j
  else if 0 <= i < len
    then true
  else if 0 <= j < len
    then false
  else i <= j.

lemma cmp_of_rel_in_range (xs : inp list) (i j : int) :
  0 <= i < len => 0 <= j < len =>
  cmp_of_rel xs i j <=> rel xs i j.
proof.
rewrite /cmp_of_rel /#.
qed.

lemma cmp_of_rel_pair_eq (xs : inp list) (p : int * int) :
  total_ordering xs =>
  0 <= p.`1 < len => 0 <= p.`2 < len =>
  cmp_of_rel xs p.`1 p.`2 = nth witness xs (enc p).
proof.
move => to_xs p1_rng p2_rng.
rewrite cmp_of_rel_in_range // /rel.
rewrite (nth_change_dfl false witness).
rewrite total_ordering_size // enc_bounds //.
smt().
qed.

op nosmt cmp_tot_ord (xs: inp list) : bool =
  size xs = arity /\
  (* reflexivity *)
  (forall (i : int), cmp_of_rel xs i i) /\
  (* transitivity *)
  (forall (j i k : int),
   cmp_of_rel xs i j => cmp_of_rel xs j k => cmp_of_rel xs i k) /\
  (* antisymmetry *)
  (forall (i j : int),
   cmp_of_rel xs i j => cmp_of_rel xs j i => i = j) /\
  (* totality *)
  (forall (i j : int), cmp_of_rel xs i j \/ cmp_of_rel xs j i).

lemma cmp_tot_ord_size (xs : inp list) :
  cmp_tot_ord xs => size xs = arity.
proof. rewrite /cmp_tot_ord /#. qed.

lemma cmp_tot_ord_refl (xs : inp list, i : int) :
  cmp_tot_ord xs  => cmp_of_rel xs i i.
proof. rewrite /cmp_tot_ord /#. qed.

lemma cmp_tot_ord_trans (xs : inp list, j i k : int) :
  cmp_tot_ord xs =>
  cmp_of_rel xs i j => cmp_of_rel xs j k => cmp_of_rel xs i k.
proof. rewrite /cmp_tot_ord /#. qed.

lemma cmp_tot_ord_antisym (xs : inp list, i j : int) :
  cmp_tot_ord xs =>
  cmp_of_rel xs i j => cmp_of_rel xs j i => i = j.
proof. rewrite /cmp_tot_ord /#. qed.

lemma cmp_tot_ord_total (xs : inp list, i j : int) :
  cmp_tot_ord xs =>
  cmp_of_rel xs i j \/ cmp_of_rel xs j i.
proof. rewrite /cmp_tot_ord /#. qed.

lemma cmp_tot_ord_ne_not_sym (xs : inp list, i j : int) :
  cmp_tot_ord xs => i <> j =>
  cmp_of_rel xs i j => ! cmp_of_rel xs j i.
proof. rewrite /cmp_tot_ord /#. qed.

lemma cmp_tot_ord_of_tot_ord (xs : inp list):
  total_ordering xs => cmp_tot_ord xs.
proof.
rewrite /total_ordering /cmp_tot_ord /cmp_of_rel /#.
qed.

(* sort using the comparision function of a total ordering *)

op tsort (xs : inp list) (bs : int list) : int list =
   sort (cmp_of_rel xs) bs.

(* test whether sorted using the comparision function of a total ordering *)

op tsorted (xs: inp list) (bs : int list) : bool =
   sorted (cmp_of_rel xs) bs.

(* the list 0 .. len - 1 *)

op range_len : int list = range 0 len.

lemma size_range_len :
  size range_len = len.
proof.
by rewrite /range_len size_range /= ler_maxr 1:ge0_len.
qed.

lemma in_range_len (n : int) :
  n \in range_len <=> 0 <= n < len.
proof.
by rewrite /range_len mem_range.
qed.

lemma uniq_range_len : uniq range_len.
proof.
rewrite /range_len range_uniq.
qed.

(* all permutations of 0 .. len - 1 *)

op perms_len : int list list = allperms range_len.

lemma size_perms_len : size perms_len = fact len.
proof.
by rewrite /perms_len size_allperms_uniq /range_len 1:range_uniq
           size_range /= ler_maxr 1:ge0_len.
qed.

(* convert a total ordering into a permutation on 0 .. len - 1 *)

op total_ordering_to_perm_len (xs : inp list) : int list =
  tsort xs range_len.

lemma pathP (def: 'a, e : 'a -> 'a -> bool, x : 'a, xs : 'a list) :
  path e x xs <=>
  xs = [] \/ e x (head def xs) /\ sorted e xs.
proof. by case xs. qed.

lemma cmp_head_ne_path (def: 'a, e : 'a -> 'a -> bool, x : 'a, xs : 'a list) :
  path e x xs => xs <> [] => e x (head def xs).
proof.
rewrite (pathP def e) => [[|] //].
qed.

lemma cmp_head_path_same_def (e : 'a -> 'a -> bool, x : 'a, ys : 'a list) :
  (forall (a : 'a), e a a) => path e x ys => e x (head x ys).
proof.
move => refl_e.
case ys => [| //].
rewrite /= refl_e.
qed.

lemma sorted_nthP (def : 'a, e : 'a -> 'a -> bool, xs : 'a list) :
  sorted e xs <=>
  (forall (i : int),
   0 <= i < size xs - 1 => e (nth def xs i) (nth def xs (i + 1))).
proof.
split.
elim xs =>
  [/= i [ge0_i lt_i_min1] |
   x xs IH /= path_e_x_xs i [ge0_i lt_i_size_xs]].
have // : 0 < -1 by rewrite (ler_lt_trans i).
case (i = 0) => [eq0_i | ne0_i].
case (i + 1 = 0) => [| ne0_i_plus1].
by rewrite eq0_i.
have ne_nil_xs : xs <> [] by rewrite -size_eq0 1:ltr0_neq0 1:-eq0_i.
by rewrite eq0_i nth0_head cmp_head_ne_path.
case (i + 1 = 0) => [eq0_i_plus1 | ne0_i_plus1].
have // : i + 1 <> 0 by rewrite ltr0_neq0 1:ltr_spaddr.
rewrite IH 1:(path_sorted _ x) //.
split => [| _].
by rewrite ler_subr_addr -ltzE ltr_def.
by rewrite ltr_add2r.
elim xs => [// | x xs IH srtd_x_cons_xsP /=].
rewrite (pathP def e).
case (xs = []) => [// | ne_xs_nil].
right.
split.
rewrite -nth0_head.
have -> : x = nth def (x :: xs) 0 by trivial.
have -> : nth def xs 0 = nth def (x :: xs) 1 by trivial.
rewrite srtd_x_cons_xsP /=.
rewrite -size_eq0 in ne_xs_nil.
rewrite ltr_def ne_xs_nil /= size_ge0.
rewrite IH => i [ge0_i lt_i_size_xs_min1].
have -> : nth def xs i = nth def (x :: xs) (i + 1).
  rewrite /=.
  have -> // : i + 1 <> 0.
  by rewrite gtr_eqF 1:ltr_spaddr.
have -> : nth def xs (i + 1) = nth def (x :: xs) ((i + 1) + 1).
  rewrite /=.
  have -> // : i + 2 <> 0.
  by rewrite gtr_eqF 1:ltr_spaddr.
rewrite srtd_x_cons_xsP /=.
split => [| _].
by rewrite addr_ge0.
by rewrite ltr_subr_addr in lt_i_size_xs_min1.
qed.

lemma sorted_nth (def : 'a, ms : 'a list, e : 'a -> 'a -> bool, k l : int) :
  (forall (x : 'a), e x x) =>
  (forall (y x z : 'a), e x y => e y z => e x z) =>
  sorted e ms => 0 <= k <= l < size ms =>
  e (nth def ms k) (nth def ms l).
proof.
move => refl_e trans_e sorted_e_ms [#] ge0_k.
have H :
  forall (l : int),
  0 <= l => k <= l < size ms => e (nth def ms k) (nth def ms l).
  elim => [[le0_k _] | l' ge0_l' IH [le_k_l'_plus1 l'_plus1_lt_size_ms]].
  have -> : k = 0 by apply ler_anti.
  rewrite refl_e.
  case (k = l' + 1) => [-> | lt_k_l'_plus1].
  rewrite refl_e.
  rewrite (trans_e (nth def ms l')) 1:IH.
  split => [| _].
  by rewrite -ltzS ltr_def eq_sym.
  by rewrite (ltr_trans (l' + 1)) // ltr_spaddr.
  have [H _] := sorted_nthP def e ms.
  by rewrite H // ge0_l' /= ltr_subr_addl addrC.
move => le_k_l lt_l_size_ms; by rewrite H 1:(ler_trans k).
qed.

lemma mem_nth_exists (xs : 'a list, x : 'a):
  x \in xs =>
  exists (i : int), 0 <= i < size xs /\ nth witness xs i = x.
proof.
move => x_in_xs.
have [i onth_xs_i_eq] :=  onth_mem x xs _ => //.
exists i; by apply onth_some.
qed.

lemma sorted_exists_nth (ms : 'a list, e : 'a -> 'a -> bool, x y : 'a) :
  (forall (x : 'a), e x x) =>
  (forall (y x z : 'a), e x y => e y z => e x z) =>
  (forall (x y : 'a), e x y => e y x => x = y) =>
  sorted e ms => x \in ms => y \in ms => e x y =>
  exists (k l : int),
  0 <= k < size ms /\ 0 <= l < size ms /\ k <= l /\
  nth witness ms k = x /\ nth witness ms l = y.
proof.
move => refl_e trans_e antisym_e sorted_e_ms x_in_ms y_in_ms e_x_y.
have [k] [#] ge0_k lt_k_size_ms nth_ms_k_eq_x := mem_nth_exists ms x _ => //.
case (x = y) => [<- | ne_x_y].
by exists k k.
have [l] [#] ge0_l lt_l_size_ms nth_ms_l_eq_y := mem_nth_exists ms y _ => //.
exists k l => />.
case (k <= l) => [// | lt_l_k].
rewrite -ltrNge in lt_l_k.
have le_l_k : l <= k by rewrite ltzW.
have e_y_x : e y x.
  by rewrite -nth_ms_k_eq_x -nth_ms_l_eq_y sorted_nth.
have // : x = y by rewrite (antisym_e x y).
qed.

lemma diff_equal_size_index_diff (xs ys : bool list) :
  xs <> ys => size xs = size ys =>
  (exists (i : int),
   0 <= i < size xs /\ nth false xs i <> nth false ys i).
proof.
move => eq_size ne_xs_ys.
case
  (exists i,
   (0 <= i && i < size xs) /\ nth false xs i <> nth false ys i) =>
  [// |].
have -> H :
  (! (exists (i : int),
      (0 <= i && i < size xs) /\ nth false xs i <> nth false ys i)) =
  (forall (i : int), 0 <= i < size xs => nth false xs i = nth false ys i).
  smt().
have // : xs = ys.
by rewrite (eq_from_nth false xs ys).
qed.

lemma total_ordering_to_perm_len_good (xs : inp list) :
  total_ordering xs =>
  total_ordering_to_perm_len xs \in perms_len.
proof.
move => tot_ord_xs.
rewrite /total_ordering_to_perm_len /tsort /range_len /perms_len.
rewrite allpermsP perm_eq_sym perm_sort.
qed.

lemma total_ordering_to_perm_len_injective (xs ys : inp list) :
  total_ordering xs => total_ordering ys =>
  total_ordering_to_perm_len xs = total_ordering_to_perm_len ys =>
  xs = ys.
proof.
move : xs ys.
have H :
  forall (xs ys : inp list, i : int),
  total_ordering xs => total_ordering ys =>
  total_ordering_to_perm_len xs = total_ordering_to_perm_len ys =>
  0 <= i < arity => nth false xs i => ! nth false ys i => false.
  move => xs ys i tot_ord_xs tot_ord_ys.
  have -> : arity = size xs by smt(total_ordering_size).
  rewrite /total_ordering_to_perm_len /tsort =>
    eq_sort_xs_sort_ys [ge0_i lt_i_size_xs] xs_i_true ys_i_false.
  pose j := (dec i).`1.
  pose k := (dec i).`2.
  have j_rng : 0 <= j < len.
    rewrite /j dec_bounds_left; smt(total_ordering_size).
  have k_rng : 0 <= k < len.
    rewrite /k dec_bounds_right; smt(total_ordering_size).
  have le_xs_j_k : rel xs j k.
    rewrite /rel /j /k.
    have -> : ((dec i).`1, (dec i).`2) = dec i by smt().
    rewrite decK //; smt(total_ordering_size).
  have lt_ys_k_j : ! rel ys j k.
    rewrite /rel /j /k.
    have -> : ((dec i).`1, (dec i).`2) = dec i by smt().
    rewrite decK //; smt(total_ordering_size).
  have sorted_sort_by_xs :
    sorted (cmp_of_rel xs) (sort (cmp_of_rel xs) (range_len)).
    rewrite sort_sorted.
    move => x y; by rewrite cmp_tot_ord_total cmp_tot_ord_of_tot_ord.
  have sorted_sort_by_ys :
    sorted (cmp_of_rel ys) (sort (cmp_of_rel ys) (range_len)).
    rewrite sort_sorted.
    move => x y; by rewrite cmp_tot_ord_total cmp_tot_ord_of_tot_ord.
  have [l m] [#] ge0_l lt_l_len ge0_m lt_m_len le_l_m
       nth_sort_xs_l_eq_j nth_sort_xs_m_eq_k
       := sorted_exists_nth (sort (cmp_of_rel xs) (range_len))
          (cmp_of_rel xs) j k _ _ _ _ _ _ _ => //.
    move => x; by rewrite cmp_tot_ord_refl cmp_tot_ord_of_tot_ord.
    move => y x z cmp_xs_x_y cmp_xs_y_z.
    by rewrite (cmp_tot_ord_trans xs y) 1:cmp_tot_ord_of_tot_ord.
    move => x y cmp_xs_x_y cmp_xs_y_z.
    by rewrite (cmp_tot_ord_antisym xs x y) 1:cmp_tot_ord_of_tot_ord.
    rewrite mem_sort; smt(mem_range).
    rewrite mem_sort; smt(mem_range).
  have nth_sort_ys_l_eq_j :
    nth witness (sort (cmp_of_rel ys) (range_len)) l = j.
    by rewrite -eq_sort_xs_sort_ys nth_sort_xs_l_eq_j.
  have nth_sort_ys_m_eq_k :
    nth witness (sort (cmp_of_rel ys) (range_len)) m = k.
    by rewrite -eq_sort_xs_sort_ys nth_sort_xs_m_eq_k.
  have cmp_of_rel_ys_j_k : cmp_of_rel ys j k.
    rewrite -nth_sort_ys_l_eq_j -nth_sort_ys_m_eq_k.
    rewrite (sorted_nth _ _ (cmp_of_rel ys)) //.
    move => x; by rewrite cmp_tot_ord_refl 1:cmp_tot_ord_of_tot_ord.
    move => y x z cmp_ys_x_y cmp_ys_y_z.
    by rewrite (cmp_tot_ord_trans ys y) 1:cmp_tot_ord_of_tot_ord.
    smt().
  have // : rel ys j k by smt(cmp_of_rel_in_range).
move => xs ys tot_ord_xs tot_ord_ys eq_tot_ord_to_perm_len_xs_ys.
case (xs = ys) => [// | ne_xs_ys].
have [i [ge0_i lt_i_size_xs]] := diff_equal_size_index_diff xs ys _ _ => //.
  rewrite total_ordering_size //.
  rewrite total_ordering_size //.
case (nth false xs i) => [xs_i_true | xs_i_false].
rewrite (H xs ys i) // 2:/#; smt(total_ordering_size).
rewrite (H ys xs i) // 1:eq_sym // 2:/#; smt(total_ordering_size).
qed.

(* convert a permutation on 0 .. len - 1 to a total ordering *)

op perm_len_to_total_ordering (ms : int list) : inp list =
  mkseq
  (fun (i : int) =>
     index ((dec i).`1) ms <= index ((dec i).`2) ms)
  arity.

lemma perm_len_to_total_ordering_good (ms : int list) :
  ms \in perms_len =>
  total_ordering (perm_len_to_total_ordering ms).
proof.
rewrite /perms_len /perm_len_to_total_ordering /total_ordering.
move => ms_perm_len; progress.
(* size *)
rewrite size_mkseq. smt(ge0_arity).
(* reflexivity *)
by rewrite /rel nth_mkseq //= 1:enc_bounds //= encK.
(* transitivity *)
rewrite /rel nth_mkseq //= 1:enc_bounds //= in H5.
rewrite /rel nth_mkseq //= 1:enc_bounds //= in H6.
rewrite /rel nth_mkseq //= 1:enc_bounds //.
smt(encK).
(* anti-sym *)
rewrite /rel nth_mkseq //= 1:enc_bounds //= in H3.
rewrite /rel nth_mkseq //= 1:enc_bounds //= in H4.
  have eq_idx : index i ms = index j ms by smt(encK).
  have eq_nth_i :
    nth 0 ms (index i ms) = i by smt(allpermsP nth_index mem_range perm_eq_mem).
  have eq_nth_j :
    nth 0 ms (index j ms) = j by smt(allpermsP nth_index mem_range perm_eq_mem).
rewrite -eq_nth_i -eq_nth_j /#.
(* totality *)
rewrite /rel !nth_mkseq 1:enc_bounds //= 1:enc_bounds // !encK //.
have eq_nth_i :
  nth 0 ms (index i ms) = i by smt(allpermsP nth_index mem_range perm_eq_mem).
have eq_nth_j :
  nth 0 ms (index j ms) = j by smt(allpermsP nth_index mem_range perm_eq_mem).
have /# : (index i ms) <> (index j ms) by smt().
qed.

lemma perm_len_to_total_ordering_indices (ms : int list, i j : int) :
  ms \in perms_len => 0 <= i < len => 0 <= j < len =>
  cmp_of_rel (perm_len_to_total_ordering ms) i j <=> index i ms <= index j ms.
proof.
move => ms_in_perms_len range_i range_j.
by rewrite cmp_of_rel_in_range // /perm_len_to_total_ordering
          /rel nth_mkseq 1:enc_bounds //= !encK.
qed.

lemma perm_len_to_total_orderingK (ms : int list) :
  ms \in perms_len =>
  total_ordering_to_perm_len (perm_len_to_total_ordering ms) = ms.
proof.
rewrite /total_ordering_to_perm_len /tsort => ms_in_perms_len.
have perm_eq_ms_range_len : perm_eq ms range_len.
  by rewrite perm_eq_sym -allpermsP.
have uniq_ms : uniq ms by rewrite (perm_eq_uniq _ range_len) // range_uniq.
pose tot := perm_len_to_total_ordering ms.
have tot_ord : total_ordering tot by rewrite perm_len_to_total_ordering_good.
have cmp_tot_ord_tot : cmp_tot_ord tot by rewrite cmp_tot_ord_of_tot_ord.
have cto_total := cmp_tot_ord_total tot.
have cto_trans := cmp_tot_ord_trans tot.
have cto_antisym := cmp_tot_ord_antisym tot.
have <- : sort (cmp_of_rel tot) ms = sort (cmp_of_rel tot) range_len.
  rewrite -perm_sortP /#.
rewrite sort_id // 1..3:/#.
rewrite (sorted_nthP witness) => i [ge0_i lt_i_size_minus1].
rewrite perm_len_to_total_ordering_indices //;
  first 2 rewrite -mem_range -(perm_eq_mem ms) // mem_nth /#.
rewrite !index_uniq //#.
qed.

(* now we can define our f and show it has the correct property: *)

type out = int list.

op f (aux : aux, xs : inp list) : out option =
  if total_ordering xs
  then Some (total_ordering_to_perm_len xs)
  else None.

(* the algorithm tries to compute f () xs, i.e., the result
   of sorting the list 0 .. len - 1 using cmp_of_rel xs,
   though making queries about how indices are related by
   cmp_of_rel xs *)

lemma f_prop (xs : inp list) :
  total_ordering xs =>
  is_some (f () xs) /\ perm_eq (oget (f () xs)) range_len /\
  tsorted xs (oget (f () xs)).
proof.
move => tot_ord_xs.
rewrite /f tot_ord_xs /=.
split.
by rewrite perm_eq_sym -allpermsP total_ordering_to_perm_len_good.
rewrite /tsorted /total_ordering_to_perm_len /tsort sort_sorted.
move => i j; by rewrite cmp_tot_ord_total cmp_tot_ord_of_tot_ord.
qed.

lemma f_is_some (xs : inp list) :
  total_ordering xs => is_some (f () xs).
proof.
move => tot_ord_xs.
smt(f_prop).
qed.

lemma f_is_perm_len (xs : inp list) :
  total_ordering xs => perm_eq (oget (f () xs)) range_len.
proof.
move => tot_ord_xs.
smt(f_prop).
qed.

lemma f_sorted (xs : inp list) :
  total_ordering xs => tsorted xs (oget (f () xs)).
proof.
move => tot_ord_xs.
smt(f_prop).
qed.

lemma f_bad (xs : inp list) :
  ! total_ordering xs => f () xs = None.
proof. smt(). qed.

clone export Bounds as B with
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
  elim H; first smt(total_ordering_size).
  elim; first smt(allP).
  smt().
by rewrite f_bad.
qed.
(* end of realization *)
