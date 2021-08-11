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

require import AllCore List IntDiv StdOrder IntMin FSetAux Perms Binomial.
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

  (* sort with total ordering*)

op cmp_of_rel (xs: inp list) (x , y : int) : bool =
  if (0 <= x < len /\ 0 <= y < len)
  then rel xs x y
  else  if (0 <= x < len) then true
  else  if (0 <= y < len) then false
  else  x <= y.

op nosmt cmp_total_ordering (xs: inp list) : bool =
  size xs = arity /\
  (forall (i : int), cmp_of_rel xs i i) /\
  (forall (i j k : int),
    cmp_of_rel xs i j => cmp_of_rel xs j k => cmp_of_rel xs i k) /\
  (forall (i j : int),
    cmp_of_rel xs i j => cmp_of_rel xs j i => i = j) /\
  forall (i j : int),
    i <> j => cmp_of_rel xs i j \/ cmp_of_rel xs j i.

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
  cmp_total_ordering xs =>
   i <> j =>
  cmp_of_rel xs i j => ! cmp_of_rel xs j i.
proof. rewrite /cmp_total_ordering /#. qed.
  

lemma tot_cmp_tot (xs:inp list):
    total_ordering xs => cmp_total_ordering (xs).
proof.
  rewrite /cmp_total_ordering /total_ordering => //.
  smt().
qed.    

op tsort (xs: inp list) (s: int list) =
   sort ( cmp_of_rel xs  ) s.

op tsorted (xs: inp list) (s: int list) =
   sorted ( cmp_of_rel xs ) s.


lemma sorted_perm_exists (xs : inp list) :
  total_ordering xs =>
  exists (perm : int list),
  perm_eq (range 0 len) perm /\ tsorted xs perm.
proof.
move => tot_ord_xs.
have H :
  forall (n : int),
  0 <= n => n <= len =>
  exists (perm : int list),
  perm_eq (range 0 n) perm  /\ tsorted xs perm.
  move => n ge0_n le_n_len.
  exists (sort (cmp_of_rel xs) (range 0 (n))).
  split.
  smt(perm_eq_sym perm_sort).
  rewrite /tsorted.
  rewrite (sort_sorted).
  smt(tot_cmp_tot cmp_total_ordering_total).
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


op sorted_perm_len_rel (xs : inp list, perm : int list) : bool =
  perm_eq (range 0 len) perm /\ tsorted xs perm.

lemma sorted_perm_rel_exists (xs : inp list) :
  total_ordering xs =>
  exists (perm : int list), sorted_perm_len_rel xs perm.
proof. apply sorted_perm_exists. qed.

lemma sorted_perm_len_rel_uniq (xs : inp list, perm1 perm2 : int list) :
  total_ordering xs =>
  sorted_perm_len_rel xs perm1 => sorted_perm_len_rel xs perm2 =>
  perm1 = perm2.
proof.
move => tot_ord_xs [ispl1 srted1] [ispl2 srted2]. print eq_sorted.
  rewrite (eq_sorted (cmp_of_rel xs) _ _ perm1 perm2).
  smt(cmp_total_ordering_trans tot_cmp_tot).
  smt(cmp_total_ordering_antisym tot_cmp_tot).
  smt().
  smt().
  smt(perm_eq_trans perm_eq_sym).
  trivial.
qed.

(* now we can define our f and show it has the correct property *)

type out = int list.

op f (aux : aux, xs : inp list) : out option =
  if total_ordering xs
  then Some (tsort xs (range 0 len) )
  else None.

lemma f_prop (xs : inp list) :
  total_ordering xs =>
  is_some (f () xs) /\ perm_eq (range 0 len) (oget (f () xs)) /\
  tsorted xs (oget (f () xs)).
proof.
move => tot_ord_xs.
  split.
  smt(sorted_perm_exists).
  split.
  rewrite /f /sorted_perm_len_rel tot_ord_xs => /=.
  smt(perm_eq_sym perm_sort).
  rewrite /tsort /f tot_ord_xs /tsorted /tsort => /=. 
  smt(sort_sorted cmp_total_ordering_total tot_cmp_tot).
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

(* The adversary *)

module Adv : ADV = {

  var inpss : inp list list  (* current possible lists of inputs *)
  
  proc init() : unit = {
    inpss <- init_inpss ();
    return ();       
  }

  proc ans_query(i: int) : inp = {
    (* var fst, snd : int ; *) (* stores the dec indices *)
    var inpss_t, inpss_f : inp list list; (* two possible inpss sizes when the adversary answers true or false *) 
    var ret : inp; 
  
    inpss_t <- (filter_nth inpss i true);
    inpss_f <- (filter_nth inpss i false);      

    if (size(inpss_t) <= size(inpss_f)){
      inpss <- filter_nth inpss i false;  (*answering false remains more possible inpust*)
      ret <- false;     
      }
    else {
       (* this also covers:  1. the algorithm asks the rel of (i, i);
                             2. (i, j) is asked before and this time (j, i);
                             3. (i, j) = true, (j, k) = true,  this time asks (i,k), etc *)
      inpss <- filter_nth inpss i true;  
      ret <- true ;  
    }
    return ret;   
  }
}.    

(* adversary is lossless *)

lemma Adv_init_ll : islossless Adv.init.
proof.
proc; auto.
qed.

lemma Adv_ans_query_ll : islossless Adv.ans_query.
proof.
proc; auto.
qed.



(* here is our main theorem: *)

lemma G_Adv_main (Alg <: ALG{Adv}) : 
  hoare [G(Alg, Adv).main : true ==> res.`1 \/ int_log_up 2 (fact len) <= res.`2].
proof.
  admit.
qed.
    
