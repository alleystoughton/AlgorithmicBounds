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

require AdvLowerBounds.   (* adversarial lower bounds framework *)
require import ListSizesInjectionSurjection.
require import AllLists.  (* generating all lists of length over universe *)
require import IntLog.    (* integer logarithms *)
require import IntDiv2.   (* division by powers of two *)

op len : int.

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

(* sort with total ordering *)

op cmp_of_rel (xs : inp list) (x y : int) : bool =
  if 0 <= x < len /\ 0 <= y < len
    then rel xs x y
  else if 0 <= x < len
    then true
  else if 0 <= y < len
    then false
  else x <= y.

op nosmt cmp_total_ordering (xs: inp list) : bool =
  size xs = arity /\
  (forall (i : int), cmp_of_rel xs i i) /\
  (forall (i j k : int),
   cmp_of_rel xs i j => cmp_of_rel xs j k => cmp_of_rel xs i k) /\
  (forall (i j : int),
   cmp_of_rel xs i j => cmp_of_rel xs j i => i = j) /\
  (forall (i j : int),
   i <> j => cmp_of_rel xs i j \/ cmp_of_rel xs j i).

lemma cmp_total_ordering_size (xs : inp list) :
  cmp_total_ordering xs => size xs = arity.
proof. rewrite /cmp_total_ordering /#. qed.

lemma cmp_total_ordering_refl (xs : inp list, i : int) :
  cmp_total_ordering xs  => cmp_of_rel xs i i.
proof. rewrite /cmp_total_ordering /#. qed.

lemma cmp_total_ordering_trans (xs : inp list, j i k : int) :
  cmp_total_ordering xs =>
  cmp_of_rel xs i j => cmp_of_rel xs j k => cmp_of_rel xs i k.
proof. rewrite /cmp_total_ordering /#. qed.

lemma cmp_total_ordering_antisym (xs : inp list, i j : int) :
  cmp_total_ordering xs =>
  cmp_of_rel xs i j => cmp_of_rel xs j i => i = j.
proof. rewrite /cmp_total_ordering /#. qed.

lemma cmp_total_ordering_total (xs : inp list, i j : int) :
  cmp_total_ordering xs =>
  cmp_of_rel xs i j \/ cmp_of_rel xs j i.
proof. rewrite /cmp_total_ordering /#. qed.

lemma cmp_total_ordering_ne_not_sym (xs : inp list, i j : int) :
  cmp_total_ordering xs => i <> j =>
  cmp_of_rel xs i j => ! cmp_of_rel xs j i.
proof. rewrite /cmp_total_ordering /#. qed.

lemma tot_cmp_tot (xs:inp list):
  total_ordering xs => cmp_total_ordering (xs).
proof.
rewrite /cmp_total_ordering /total_ordering => //.
smt().
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

lemma nth_cons0 (x : 'a, ys : 'a list) :
  nth witness (x :: ys) 0 = x.
    proof. trivial. qed.

lemma nth_cons_pos (x : 'a, ys : 'a list, i : int) :
  0 <= i < size ys =>
  nth witness (x :: ys) (i + 1) = nth witness ys i.
    proof. smt(). qed.
  
lemma sorted_nth_gen (ms : 'a list, e : 'a -> 'a -> bool) :
  (forall (x y : 'a), e x y \/ e y x) =>
  (forall (y x z : 'a), e x y => e y z => e x z) =>
  (forall (x y : 'a), e x y => e y x => x = y) =>
  sorted e ms => (forall (k l: int), 0 <= k <= l < size ms =>
  e (nth witness ms k) (nth witness ms l)).
proof.
move =>  tot_e trans_e antisym_e.
elim ms.
rewrite /= /#.
move => x xs IH sorted_cons /=.
  have path_x_xs : path e x xs by smt().
move => k0 l0.
case (k0=0) => [ //= eq0_k0 | //= neq0_k0 [#] ge0_k0 le_k0_l0 lt_size_l0 ] .
case (l0=0)=> [/# | //= neq0_l0 [#] ge0_k0 le_k0_l0 lt_size_l0 ].
have all_exs : all (e x) xs by smt( order_path_min). 
rewrite allP in all_exs.
smt(mem_nth).
have -> //= : ! (l0 = 0) by smt(). 
have sorted_xs : sorted e xs by smt(path_sorted).
apply IH ; auto.
smt().
qed.

  
lemma sorted_nth (ms : 'a list, e : 'a -> 'a -> bool, k l : int) :
  (forall (x y : 'a), e x y \/ e y x) =>
  (forall (y x z : 'a), e x y => e y z => e x z) =>
  (forall (x y : 'a), e x y => e y x => x = y) =>
  sorted e ms => 0 <= k <= l < size ms =>
  e (nth witness ms k) (nth witness ms l).
proof.
move => tot_e trans_e antisym_e sorted_e_ms.
move : k l.
by apply sorted_nth_gen.
qed.

lemma nth_exists (xs:'a list):
    forall x, x \in xs => exists i, 0<=i < size xs /\ nth witness xs i = x.
proof.
move => x x_in_xs.  
have [i onth_xs_i_eq ] :=  onth_mem x xs _ => //=.
exists i; by apply onth_some.
(* elim xs. *)
(* rewrite /= /#. *)
(* move => m ms ih  x [#] x_in_cons. *)
(* elim x_in_cons => [eq_x_m //= | x_in_ms]. *)
(* exists 0. split. smt(size_ge0). smt(). *)
(* apply ih in x_in_ms. *)
(* elim x_in_ms => [i [#]  ge0_i lt_i_size  nth_ms_x_eq_x]. *)
(* exists (i+1). *)
(* smt(size_ge0 nth_cons_pos ). *)
(* qed. *)
qed.

lemma sorted_exists_nth (ms : 'a list, e : 'a -> 'a -> bool, x y : 'a) :
  (forall (x y : 'a), e x y \/ e y x) =>
  (forall (y x z : 'a), e x y => e y z => e x z) =>
  (forall (x y : 'a), e x y => e y x => x = y) =>
  sorted e ms => x \in ms => y \in ms => e x y =>
  exists (k l : int),
  0 <= k < size ms /\ 0 <= l < size ms /\ k <= l /\
  nth witness ms k = x /\ nth witness ms l = y.
proof.
move => tot_e trans_e antisym_e.
elim ms.
rewrite /= /#.
move => m xs ih sorted_cons  x_in_cons  y_in_cons e_x_y.
elim x_in_cons => [eq_x_m //= | b ].
elim y_in_cons => [eq_y_m //= | y_in_xs].
exists 0 0 => //= ; smt(size_ge0).
exists 0 => //=. 
case (y=m) => [eq_y_m| neq_y_m].
exists 0 => //= ; smt(size_ge0).
apply (nth_exists xs y) in y_in_xs.
elim y_in_xs => /= [i [#] ge0_i lt_i_size nth_x_i_eq_y].
exists (i+1); progress => //=; smt(size_ge0). 
elim y_in_cons => [eq_y_m //= | y_in_xs //=].
exists 0 0 => //=. 
progress => //=.
smt(size_ge0). smt(size_ge0). 
  have path_e_m_xs: path e m xs by smt().
  have all_exs : all (e m) xs by smt (order_path_min).
rewrite allP in all_exs.
smt(). smt().
  have path_e_m_xs: path e m xs by   smt().
  have sorted_xs : sorted e xs by smt(path_sorted).
  have ihs : exists (k l : int),
      (0 <= k && k < size xs) /\
      (0 <= l && l < size xs) /\
      k <= l /\ nth witness xs k = x /\ nth witness xs l = y by smt().
elim ihs => //= [k l [#]  ge0_k lt_k_size ge0_l lt_k_size_xs le_lk_l  nth_xs_k_eq_x nth_x_l_eq_y].      
exists (k+1) (l+1). progress; smt(). 
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
    sorted (cmp_of_rel xs) (sort (cmp_of_rel xs) (range 0 len)).
    rewrite sort_sorted.
    move => x y; by rewrite cmp_total_ordering_total tot_cmp_tot.
  have sorted_sort_by_ys :
    sorted (cmp_of_rel ys) (sort (cmp_of_rel ys) (range 0 len)).
    rewrite sort_sorted.
    move => x y; by rewrite cmp_total_ordering_total tot_cmp_tot.
  have := sorted_exists_nth (sort (cmp_of_rel xs) (range 0 len))
          (cmp_of_rel xs) j k _ _ _ _ _ _ _ => //.
    move => x y; by rewrite cmp_total_ordering_total tot_cmp_tot.
    move => y x z cmp_xs_x_y cmp_xs_y_z.
    by rewrite (cmp_total_ordering_trans xs y) 1:tot_cmp_tot.
    move => x y cmp_xs_x_y cmp_xs_y_z.
    by rewrite (cmp_total_ordering_antisym xs x y) 1:tot_cmp_tot.
    rewrite mem_sort; smt(mem_range).
    rewrite mem_sort; smt(mem_range).
  move =>
    [l m] [#] ge0_l lt_l_len ge0_m lt_m_len le_l_m
    nth_sort_xs_l_eq_j nth_sort_xs_m_eq_k.
  have nth_sort_ys_l_eq_j :
    nth witness (sort (cmp_of_rel ys) (range 0 len)) l = j.
    by rewrite -eq_sort_xs_sort_ys nth_sort_xs_l_eq_j.
  have nth_sort_ys_m_eq_k :
    nth witness (sort (cmp_of_rel ys) (range 0 len)) m = k.
    by rewrite -eq_sort_xs_sort_ys nth_sort_xs_m_eq_k.
  have cmp_of_rel_ys_j_k : cmp_of_rel ys j k.
    rewrite -nth_sort_ys_l_eq_j -nth_sort_ys_m_eq_k.
    rewrite (sorted_nth _ (cmp_of_rel ys)) //.
    move => x y; by rewrite cmp_total_ordering_total tot_cmp_tot.
    move => y x z cmp_ys_x_y cmp_ys_y_z.
    by rewrite (cmp_total_ordering_trans ys y) 1:tot_cmp_tot.
    move => x y cmp_ys_x_y cmp_ys_y_z.
    by rewrite (cmp_total_ordering_antisym ys x y) 1:tot_cmp_tot.
    smt().
  have // : rel ys j k by smt().
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
admit.
qed.

lemma perm_len_to_total_orderingK (ms : int list) :
  total_ordering_to_perm_len (perm_len_to_total_ordering ms) = ms.
proof.
admit.
qed.

(* now we can define our f and show it has the correct property: *)

type out = int list.

op f (aux : aux, xs : inp list) : out option =
  if total_ordering xs
  then Some (total_ordering_to_perm_len xs)
  else None.

lemma f_prop (xs : inp list) :
  total_ordering xs =>
  is_some (f () xs) /\ perm_eq range_len (oget (f () xs)) /\
  tsorted xs (oget (f () xs)).
proof.
move => tot_ord_xs.
split => [/# |].
split.
rewrite /f tot_ord_xs /=.
rewrite perm_eq_sym /tsort perm_sort.
rewrite /tsorted /f tot_ord_xs /= sort_sorted.
move => i j.
by rewrite cmp_total_ordering_total tot_cmp_tot.
qed.

lemma f_is_some (xs : inp list) :
  total_ordering xs => is_some (f () xs).
proof.
move => tot_ord_xs.
smt(f_prop).
qed.

lemma f_is_perm_len (xs : inp list) :
  total_ordering xs => perm_eq (range 0 len) (oget (f () xs)).
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
  elim H.
  rewrite /total_ordering !negb_and => -> //.
  elim.
  have // : all (mem univ) xs by smt(allP).
  by rewrite /good.
  smt(f_bad).
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
    (* two possible inpss elements when the adversary answers true or false *) 
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
split.
rewrite mem_filter.
split.
by rewrite perm_len_to_total_ordering_good.
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

lemma filter_nth_size_b_not_b (inpss : inp list list, i : int, b : bool) :
  0 <= i < arity =>
  size inpss = size (filter_nth inpss i b) + size(filter_nth inpss i (!b)).
proof.
move => [ge0_i lt_i_arity].
rewrite /filter_nth.
elim inpss => [// | x xs IH /#].
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
proof.
rewrite ge1_fact ge0_len.
qed.

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

lemma divpow2up_next_size_ge2 (inpss : inp list list, stage i : int, b : bool) :
  0 <= stage => 0 <= i < arity => 2 <= size inpss =>
  size (filter_nth inpss i (!b)) <= size (filter_nth inpss i b) =>
  divpow2up (fact len) stage <= size inpss =>
  divpow2up (fact len) (stage + 1) <= size (filter_nth inpss i b).
proof.
move =>
  ge0_stage [ge0_i lt_i_arity] ge2_size_inpss le_size_filter_nth_not_b_b
  le_dp2u_stage_size_inpss.
rewrite (divpow2up_next_new_ub (size inpss)) 1:ge1_fact_len //.
smt(filter_nth_size_b_not_b).
qed.

(* here is our main lemma: *)

lemma G_Adv_main (Alg <: ALG{Adv}) : 
  hoare [G(Alg, Adv).main : true ==> res.`1 \/ int_log_up 2 (fact len) <= res.`2].
proof.
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

axiom log_2_0_eq_0 : int_log 2 0 = 0.
    
lemma log2_fact (n: int) :
   0<=n =>  n * (int_log 2 n ) %/ 2 <= int_log 2 (fact n). 
proof.
   have helper :0 <= n => n * (int_log 2 n +2) <= ( int_log 2 (fact n)  + 2 ^(int_log 2 n) ) *2 +1. 
   elim n => [| n ge0_n ih ]. smt(log_2_0_eq_0 fact0 int_log_ge0  expr0).
   have firstlaw : int_log 2 (fact (n+1)) = int_log 2 (fact n) + int_log 2 (n+1). 
   admit.     
   admit.   
 smt(lez_eqVlt fact0 int_log_ge0  int_logP).
  (* rewrite lez_eqVlt in ge0_n.   *)
  (* elim ge0_n => [//= | pos].    *)
  (*  smt(fact0 int_log_ge0). *)

  
  (* have half:  (n *( int_log 2 n + 2)) %/ 2 <= ( (int_log 2 (fact n) + 2 ^ int_log 2 n) * 2 + 1)%/2 by smt(). *)
 
  (*  have half_smp : ((int_log 2 (fact n) + 2 ^ int_log 2 n) * 2 + 1) %/ 2 <= (int_log 2 (fact n) + 2 ^ int_log 2 n)   by smt(). *)

  (*  have half2 :   (n *( int_log 2 n + 2)) %/ 2 = (n * (int_log 2 n) ) %/2 + n by smt(). *)
 
  (*  have half3 : (n * (int_log 2 n) ) %/2 + n -  2 ^ int_log 2 n <= int_log 2 (fact n) by smt(). *)
    
  (*     have H : 2 ^ int_log 2 n <= n by smt(int_logP). *)

  (*  smt(). *)
qed.

    
lemma log2up_fact (n: int) :
     n * (int_log_up 2 n ) %/ 2 <= int_log_up 2 (fact n). 
 proof.
   admit.
 qed.
