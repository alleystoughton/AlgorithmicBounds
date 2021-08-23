(* Application of Adversarial Lower Bounds Framework to
   Comparison-based Sorting *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2021 - Boston University
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

require import AllCore List IntDiv StdOrder IntMin FSetAux Perms Binomial.
import IntOrder.

require AdvLowerBounds.    (* adversarial lower bounds framework *)
require import ListSizes.  (* showing uniq lists have the same size *)
require import AllLists.   (* generating all lists of length over universe *)
require import IntLog.     (* integer logarithms *)
require import IntDiv2.    (* division by powers of two *)

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

(* to represent this problem using our framework, we encode queries
   (i, j), for 0 <= i, j < len, as integers between 0 and arity - 1,
   for arity = len * len: *)

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

lemma path_when_ne_head (def: 'a, e : 'a -> 'a -> bool, x : 'a, xs : 'a list) :
  path e x xs => xs <> [] => e x (head def xs).
proof.
rewrite (pathP def e) => [[|] //].
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
by rewrite eq0_i nth0_head path_when_ne_head.
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
  total_ordering xs => perm_eq (oget (f () xs)) (range_len).
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
  elim H; first smt(total_ordering_size).
  elim; first smt(allP).
  smt().
by rewrite f_bad.
qed.
(* end of realization *)

(* the adversary *)

module Adv : ADV = {
  var inpss : inp list list  (* current possible lists of inputs *)
  
  proc init() : unit = {
    inpss <- init_inpss ();
    return ();       
  }

  proc ans_query(i: int) : inp = {
    (* two possible inpss when the adversary answers true or false *) 
    var inpss_t, inpss_f : inp list list; 
    var ret : inp;  (* return value *)
  
    inpss_t <- (filter_nth inpss i true);
    inpss_f <- (filter_nth inpss i false);

    if (size inpss_t <= size inpss_f) {   (* answering false keeps as least as *)
      inpss <- filter_nth inpss i false;  (* many inputs lists as answering true *)
      ret <- false;     
    }
    else {
       (* this also covers:
            1. the algorithm asks the rel of (i, i);
            2. (i, j) is asked before and this time (j, i);
            3. (i, j) = true, (j, k) = true, this time asks (i,k), etc. *)
      inpss <- filter_nth inpss i true;  
      ret <- true ;  
    }
    return ret;   
  }
}.

lemma uniq_init_inpss :
  uniq (init_inpss ()).
proof.    
smt(inpss_invar_init inpss_invar_uniq).
qed.

lemma total_ordering_to_perm_len_lists_fun :
  lists_fun (init_inpss ()) perms_len total_ordering_to_perm_len.
proof.   
rewrite /lists_fun /init_inpss /good => xs /=.
rewrite mem_filter => [[tot_ord_xs _]].
by rewrite total_ordering_to_perm_len_good.
qed.

lemma total_ordering_to_perm_len_lists_fun_injective :
  lists_fun_injective (init_inpss ()) perms_len total_ordering_to_perm_len.
proof.
rewrite /lists_fun_injective /init_inpss /good => xs ys.
rewrite 2!mem_filter => [/= [tot_xs _] [tot_ys _]].
by apply total_ordering_to_perm_len_injective.
qed.

lemma total_ordering_to_perm_len_lists_fun_surjective :
  lists_fun_surjective (init_inpss ()) perms_len total_ordering_to_perm_len.
proof.
rewrite /lists_fun_surjective /init_inpss /good => ms ms_in_perms_len /=.
exists (perm_len_to_total_ordering ms).
split; first rewrite mem_filter.
split; first by rewrite perm_len_to_total_ordering_good.
rewrite all_lists_arity_have 1:ge0_arity.
smt(perm_len_to_total_ordering_good total_ordering_size).
rewrite allP => x _; rewrite /univ /#.
by rewrite perm_len_to_total_orderingK.
qed.

lemma init_inpss_fact_len  : 
  size (init_inpss ()) = fact len.
proof.
rewrite (uniq_sets_eq_size_if_injective_surjective (init_inpss ()) perms_len
         total_ordering_to_perm_len) //.
smt(uniq_init_inpss).
rewrite /perms; smt(uniq_allperms).
by rewrite total_ordering_to_perm_len_lists_fun.
by rewrite total_ordering_to_perm_len_lists_fun_injective.
by rewrite total_ordering_to_perm_len_lists_fun_surjective.
by rewrite size_perms_len.
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

lemma ge1_fact (n : int) :
  0 <= n => 1 <= fact n.
proof.
elim n.
by rewrite fact0.
smt(factS fact1).
qed.

lemma ge1_fact_len :
  1 <= fact len.
proof. rewrite ge1_fact ge0_len. qed.

lemma mem_implies_size_ge1 (x : 'a, ys : 'a list) :
  x \in ys => 1 <= size ys.
proof.
case ys => [| /=].
smt(in_nil).
smt(size_ge0).
qed.

lemma inpss_not_done_iff (inpss : inp list list) :
  inpss_invar () inpss =>
  ! (inpss_done () inpss) <=> 2 <= size inpss.
proof.
move => [uniq_inpss all_f_is_some].
rewrite /inpss_done.
split.
rewrite negb_forall /= => [[bs_opt /=]].
rewrite negb_forall /= => [[cs_opt /=]].
rewrite (implybE (bs_opt \in map (f tt) inpss)) negb_or /=.
rewrite (implybE (cs_opt \in map (f tt) inpss)) negb_or /=.
rewrite 2!mapP =>
  [[[xs [xs_in_inpss bs_opt_eq_f_xs]]]
   [[ys [ys_in_inpss cs_opt_eq_f_ys]]]
   ne_bs_opt_cs_opt].
have ne_xs_ys : xs <> ys by smt().
have := splitPr inpss xs _ => // [[s1 s2] inpss_eq].
rewrite inpss_eq size_cat /= addrC -addrA.
have /# : 1 <= size s2 + size s1.
have [] : ys \in s1 \/ ys \in xs :: s2 by rewrite -mem_cat /#.
smt(mem_implies_size_ge1 size_ge0).
smt(mem_implies_size_ge1 size_ge0).
move : uniq_inpss all_f_is_some.
case inpss => [// | xs inpss' /=].
case inpss' => [// | ys inpss'' /=].
rewrite negb_or.
move =>
  [#] ne_xs_ys xs_not_in_zs ys_not_in_inpss'' uniq_inpss''
  [#] is_some_f_xs is_some_f_ys all_is_some_f_inpss'' _.
have [bs f_xs_eq_Some_bs] : exists bs, f tt xs = Some bs.
  exists (oget (f tt xs)); rewrite -some_oget /#.
have [cs f_ys_eq_Some_cs] : exists cs, f tt ys = Some cs.
  exists (oget (f tt ys)); rewrite -some_oget /#.
rewrite negb_forall /=; exists (Some bs).
rewrite negb_forall /=; exists (Some cs).
rewrite implybE /= negb_or /=.
split.
left => /#.
rewrite implybE /= negb_or /=.
split.
right; left => /#.
have tot_ord_xs : total_ordering xs by smt().
have tot_ord_ys : total_ordering ys by smt().
move : ne_xs_ys.
apply contra => eq_bs_cs.
rewrite (total_ordering_to_perm_len_injective xs ys) //#.
qed.

lemma inpss_done_iff (inpss : inp list list) :
  inpss_invar () inpss => 1 <= size inpss =>
  inpss_done () inpss <=> size inpss = 1.
proof.
smt(inpss_not_done_iff).
qed.

lemma filter_nth_size_b_not_b (inpss : inp list list, i : int, b : bool) :
  0 <= i < arity =>
  size inpss = size (filter_nth inpss i b) + size(filter_nth inpss i (!b)).
proof.
move => [ge0_i lt_i_arity].
rewrite /filter_nth.
elim inpss => [// | x xs IH /#].
qed.

lemma divpow2up_next_size_ge2
      (inpss : inp list list, stage i : int, b : bool) :
  0 <= stage => 0 <= i < arity => 2 <= size inpss =>
  size (filter_nth inpss i (!b)) <= size (filter_nth inpss i b) =>
  divpow2up (fact len) stage <= size inpss =>
  divpow2up (fact len) (stage + 1) <= size (filter_nth inpss i b).
proof.
move =>
  ge0_stage [ge0_i lt_i_arity] ge2_size_inpss le_size_filter_nth_not_b_b
  le_dp2u_stage_size_inpss.
rewrite (divpow2up_next_new_ub (size inpss)) 1:ge1_fact_len //.
rewrite (filter_nth_size_b_not_b inpss i b) //#.
qed.

(* here is our main lemma, parameterized by a lower bound: *)

lemma G_Adv_main (bound : int) (Alg <: ALG{Adv}) : 
  bound <= int_log_up 2 (fact len) =>
  hoare [G(Alg, Adv).main : true ==> res.`1 \/ bound <= res.`2].
proof.
move => le_bound_ilu2_fact_len.
proc.
seq 7 :
  (inpss = init_inpss aux /\ !error /\ don = inpss_done aux inpss /\
   stage = 0 /\ queries = fset0 /\ Adv.inpss = init_inpss aux /\ aux = ()).
wp.
call (_ : true).
inline Adv.init; auto. 
while
  (stage = card queries /\ queries_in_range queries /\ Adv.inpss = inpss /\
   inpss_invar () inpss /\  don = inpss_done aux inpss /\
   divpow2up (fact len) stage <= size inpss).
seq 1 :
  (stage = card queries /\ queries_in_range queries /\ Adv.inpss = inpss /\
   inpss_invar () inpss /\ don = inpss_done aux inpss /\
   divpow2up (fact len) stage <= size inpss /\ !don /\ !error).
call (_ : true); first auto.
if.
wp.
call (_: true); first auto.
sp; elim* => stage' queries'.
inline Adv.ans_query.
sp 3.
if.
auto; progress [-delta]. 
smt(fcardUindep1).
smt(queries_in_range_add).
by rewrite inpss_invar_filter_nth.
by rewrite divpow2up_next_size_ge2 1:fcard_ge0 // 1:-inpss_not_done_iff.
auto; progress [-delta]. 
smt(fcardUindep1).
smt(queries_in_range_add).
by rewrite inpss_invar_filter_nth.
rewrite divpow2up_next_size_ge2 1:fcard_ge0 // 1:-inpss_not_done_iff //#.
auto.
auto; progress [-delta].
smt(fcards0).
smt(queries_in_range0).
rewrite inpss_invar_init.
by rewrite divpow2up_start init_inpss_fact_len.
rewrite negb_and /= in H0.
elim H0 => [inpss_done | error].
right.
rewrite (ler_trans (int_log_up 2 (fact len))) //.
apply divpow2up_eq1_int_log_up_le.
smt(ge1_fact ge1_len).
smt(fcard_ge0).
have ge1_dp2u : 1 <= divpow2up (fact len) (card queries0).
  smt(divpow2up_ge1 ge1_fact_len fcard_ge0).
apply ler_anti.
rewrite ge1_dp2u /=.
have /# : size inpss1 = 1 by rewrite -inpss_done_iff //#.
by left. 
qed.

(* here is the generalized form of our main theorem: *)

lemma lower_bound_gen (bound : int) &m :
  bound <= int_log_up 2 (fact len) =>
  exists (Adv <: ADV),
  islossless Adv.init /\ islossless Adv.ans_query /\
  forall (Alg <: ALG{Adv}),
  islossless Alg.init => islossless Alg.make_query =>
  islossless Alg.query_result =>
  Pr[G(Alg, Adv).main() @ &m : res.`1 \/ bound <= res.`2] = 1%r.
proof.
move => le_bound_ilu2_fact_len.
exists Adv.
split; first apply Adv_init_ll.
split; first apply Adv_ans_query_ll.
move => Alg Alg_init_ll Alg_make_query_ll Alg_query_result_ll.
byphoare => //.
conseq
  (_ : true ==> true)
  (_ : true ==> res.`1 \/ bound <= res.`2) => //.
apply (G_Adv_main bound Alg) => //.
rewrite (G_ll Alg Adv) 1:Alg_init_ll 1:Alg_make_query_ll
        1:Alg_query_result_ll 1:Adv_init_ll Adv_ans_query_ll.
qed.

lemma int_log2_eq_1 : int_log 2 2 = 1.
proof.
by rewrite eq_sym (int_logPuniq 2 2 1) // expr1 /= expr2.
qed.

lemma int_log_geq (x b n : int) :
  0 <= x => 2 <= b => 1 <= n =>  b^x <= n => x <= int_log b n.
proof.
move => le0_x le2_b le1_n leqn_pow_b.
rewrite -(int_log_pow_b b x) //= int_log_le //= exprn_ege1 //= 1:/#.
qed.

  
lemma log2_fact (n: int) :
   1<=n =>  (n * (int_log 2 n )) %/ 2 <= int_log 2 (fact n). 
proof.
have helper :
  0 <= n =>  1 <=n => n * (int_log 2 n +2) <= ( int_log 2 (fact n)  + 2 ^(int_log 2 n) ) *2 +1.
  (* proof of the helper *)
  elim n => [| n ge0_n ih ].
  smt( fact0 int_log_ge0  expr0).    
  move : ge0_n.  
  case (2 < n) => [ gt2_n _ _ | leq2_n ge0_n _].
  (*2 < n*)
  have : int_log 2 (n+1) = int_log 2 n \/ int_log 2 (n+1) = (int_log 2 n) + 1 /\ 2 ^(int_log 2 (n+1)) = n +1 .  
    have e1: 2 ^(int_log 2 n) <= n by rewrite int_log_lb_le //#.
    have e2: n < 2^((int_log 2 n) +1 ) by rewrite int_log_ub_lt //#. 
    have e3: 2 ^(int_log 2 (n+1)) <= n+1 by rewrite int_log_lb_le //#.
    have e4: n + 1 < 2^((int_log 2 (n+1)) +1 ) by rewrite int_log_ub_lt //#. 
    have e5:  2 ^(int_log 2 (n+1)) <=  2^( (int_log 2 n) +1 )  by rewrite /#.
    have e6: (int_log 2 (n+1)) <= (int_log 2 n ) +1
    by rewrite (ge2_exp_le_equiv 2 ( int_log 2 (n+1) ) ((int_log 2 n ) +1 ) ) //= ; smt(int_log_ge0).
    rewrite lez_eqVlt in e6.
    elim e6 => [ e7 //= | //=].
    right ; split => //#.
    rewrite ltzS lez_eqVlt => [#]  [eq_log | neq_log ].  
    by left.
    have neq_log2: (int_log 2 (n+1)) + 1 <= int_log 2 n by  smt().  
    rewrite (ge2_exp_le_equiv 2 ( (int_log 2 (n+1)) +1 ) (int_log 2 n)  ) // in neq_log2.
    smt(int_log_ge0). smt(int_log_ge0).
    (*contradiction: n +1 < n*)
    smt().
  have lb1: 2 <= int_log 2 (n+1) by  rewrite int_log_geq //=  1:/# ;   smt( ltzS  expr1 exprS).
  have lb2: (int_log 2 (n+1))  + (int_log 2 (fact n) ) <= int_log 2 (fact (n+1))
    by rewrite factS // 1:/#  (int_log_distr_mul_lb) // 1: /# ; smt(ge1_fact).
  case => [ e | [ e1 e2 ] ].
  have lb3: int_log 2 n + 2 <= (int_log 2 n ) * 2 by rewrite mul2r 1: /#. 
  rewrite e  mulzDl.
  have lb4 :  n * (int_log 2 n + 2) + (int_log 2 n + 2) <= (int_log 2 (fact n) + 2 ^ int_log 2 n) * 2 + 1 + (int_log 2 n * 2)
    by rewrite ler_add 1:ih /#.
  rewrite (lez_trans  ( (int_log 2 (fact n) + 2 ^ int_log 2 n) * 2 + 1 + int_log 2 n * 2  )) //= addzC.
  have -> //= //# : int_log 2 n * 2 + ((int_log 2 (fact n) + 2 ^ int_log 2 n) * 2 + 1)
                    = (int_log 2 n + int_log 2 (fact n) + 2 ^ int_log 2 n) * 2 + 1 by smt().
  rewrite e1  mulzDl.   
  have -> : n * (int_log 2 n + 1 + 2) + 1 * (int_log 2 n + 1 + 2) =  n * (int_log 2 n  + 2) + (int_log 2 n + 3 + n) by smt().
  have lb5 : n * (int_log 2 n + 2) +  (int_log 2 n + 3 + n)
              <= (int_log 2 (fact n) + 2 ^ int_log 2 n) * 2 + 1 +  (int_log 2 n + 3 + n)by smt(ler_add).
  rewrite (lez_trans  ( (int_log 2 (fact n) + 2 ^ int_log 2 n) * 2 + 1 + (int_log 2 n + 3 + n)  ) )  // -e1 e2 mulzDl.
  have -> :  2 ^ (int_log 2 n) * 2 = 2 ^ (int_log 2 n + 1). rewrite exprS 1:int_log_ge0 //= 1:/# /#.
  smt().
  (* n <=2  *)  
  have range_n: n =0 \/ n =1 \/ n =2  by smt().
  elim range_n  => [ eq0_n //= |[ eq1_n | eq2_n] ].
  (* n =0 *)
  rewrite eq0_n (fact1 0) //=. 
  have -> //=: int_log 2 1 = 0 by smt( int_log1_eq0 ).  
  smt(expr0).
  (* n =1 *)                  
  rewrite eq1_n //=.
  have -> : fact 2 = 2 by smt(factS fact1 fact0 expr1).
  rewrite int_log2_eq_1; smt(expr1).                  
  (* n =2 *)
  rewrite eq2_n //=.
  have -> : fact 3 = 2*3 by smt(factS fact1 fact0 expr1).
  have int_log2_3_eq_1 : 1 = int_log 2 3 by rewrite (int_logPuniq 2 3 1) //=; smt(expr1 exprS).
  smt(int_log_distr_mul_lb int_log2_eq_1 expr1 ).                       
smt(lez_eqVlt fact0 int_log_ge0  int_logP).
qed.

    
lemma log2up_fact (n: int) :
     n * (int_log_up 2 n) %/ 2 <= int_log_up 2 (fact n). 
proof.
admit.
qed.

(* here our main theorem: *)

lemma lower_bound &m :
  exists (Adv <: ADV),
  islossless Adv.init /\ islossless Adv.ans_query /\
  forall (Alg <: ALG{Adv}),
  islossless Alg.init => islossless Alg.make_query =>
  islossless Alg.query_result =>
  Pr[G(Alg, Adv).main() @ &m :
       res.`1 \/ (len %%/ 2) * int_log 2 len <= res.`2] = 1%r.
proof.
apply (lower_bound_gen (len %%/ 2 * int_log 2 len) &m _).
(* len %%/ 2 * int_log 2 len <= int_log_up 2 (fact len)

   or whatever our best approximation turns out to be *)
admit.
qed.


    
  
