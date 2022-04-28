(* Upper Bound Proof for Merge Sort Algorithm *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2021-2022 - Boston University
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

prover quorum=2 ["Alt-Ergo" "Z3"].

timeout 2.  (* can increase *)

require import AllCore List IntDiv StdOrder IntMin FSetAux Perms Binomial WF.
import IntOrder.

require import IntLog.  (* working with bounds involving integer logarithms *)

(* comparison-based sorting problem, plus bounds framework *)
require import SortingProb.
import UB.  (* upper bounds theory *)

(* wc n is a recurrence that we prove is an upper bound on the worst
   case numer of comparisons actually used by merge sort (see below)
   when given lists of distinct elements of size n (unlike in a
   conventional upper bound proof, if we had gotten the definition of
   wc wrong, our upper bound proof would have failed)

   we don't need that wc n is *equal* to the worst case number of
   comparisons actually used by merge sort, although we were able to
   experimentally check that this is true for n <= 11 *)

op wc_wf_rec_def : (int, int) wf_rec_def =
  fun (n : int,            (* input *)
       f : int -> int) =>  (* for recursive calls on < natural numbers *)
  if n <= 1  (* we only care about 1 <= n *)
  then 0
  else f (n %/ 2)  +  (* sorting the first n %/ 2 elements *)
       f (n %%/ 2) +  (* sorting the remaining elements *)
       n - 1.         (* top-level merge, in the worse case *)

(* the actual recursive definition: *)

op wc : int -> int =
  wf_recur
  lt_nat          (* well-founded relation being used *)
  0               (* element to be returned if recursive calls
                     don't respect well-founded relation *)
  wc_wf_rec_def.  (* body of recursive definition *)

lemma wc_ge0 (n : int) :
  0 <= wc n.
proof.
move : n.
apply (wf_ind lt_nat).
apply wf_lt_nat.
move => /= n IH.
rewrite /wc wf_recur 1:wf_lt_nat /wc_wf_rec_def.
case (n <= 1) => [// | gt1_n].
rewrite lerNgt /= in gt1_n.
have lt_nat_n_div2_n : lt_nat (n %/ 2) n by smt().
rewrite lt_nat_n_div2_n /=.
have lt_nat_n_div2up_n : lt_nat (n %%/ 2) n.
  smt(int_div2_up_ge1_implies_ge1 int_div2_up_lt_self_if_ge2).
rewrite lt_nat_n_div2up_n /=.
rewrite -/wc /#.
qed.

lemma wc_when_le1 (n : int) :
  n <= 1 => wc n = 0.
proof.
move => le1_n.
by rewrite /wc wf_recur 1:wf_lt_nat /wc_wf_rec_def le1_n.
qed.

lemma wc_when_ge2 (n : int) :
  2 <= n => wc n = wc (n %/ 2) + wc (n %%/ 2) + n - 1.
proof.
move => ge2_n.
rewrite /wc wf_recur 1:wf_lt_nat /wc_wf_rec_def.
have -> /= : ! n <= 1 by smt().
have -> /= : lt_nat (n %/ 2) n by smt().
have -> // : lt_nat (n %%/ 2) n.
  smt(int_div2_up_ge1_implies_ge1 int_div2_up_lt_self_if_ge2).
qed.

lemma wc_eq (n : int) :
  1 <= n => wc n = n * int_log 2 n - (2 ^ (int_log 2 n + 1) - n - 1).
proof.
move : n.
apply (wf_ind lt_nat).
apply wf_lt_nat.
move => /= n IH ge1_n.
case (n = 1) => [-> /= | ne1_n].
rewrite /wc wf_recur 1:wf_lt_nat /wc_wf_rec_def /=.
by rewrite int_log1_eq0 //= expr1.
have ge2_n : 2 <= n by smt().
rewrite /wc wf_recur 1:wf_lt_nat /wc_wf_rec_def.
have -> /= : ! (n <= 1) by smt().
have lt_nat_n_div2_n : lt_nat (n %/ 2) n by smt().
rewrite lt_nat_n_div2_n /=.
have lt_nat_n_div2up_n : lt_nat (n %%/ 2) n.
  smt(int_div2_up_ge1_implies_ge1 int_div2_up_lt_self_if_ge2).
rewrite lt_nat_n_div2up_n /=.
rewrite -/wc.
rewrite (IH (n %/ 2)) 1:/# 1:/#.
rewrite (IH (n %%/ 2)) 1:lt_nat_n_div2up_n 1:int_div2_up_ge1_implies_ge1 //.
rewrite int_log_div //=.
have -> :
  n %/ 2 * (int_log 2 n - 1) - (2 ^ int_log 2 n - n %/ 2 - 1) =
  n %/ 2 * int_log 2 n - 2 ^ (int_log 2 n) + 1 by algebra.
have -> :
 n %%/ 2 * int_log 2 (n %%/ 2) -
 (2 ^ (int_log 2 (n %%/ 2) + 1) - n %%/ 2 - 1) =
 n %%/ 2 * int_log 2 (n %%/ 2) -
 2 ^ (int_log 2 (n %%/ 2) + 1) + n %%/ 2 + 1 by algebra.
have -> :
  n * int_log 2 n - (2 ^ (int_log 2 n + 1) - n - 1) =
  n * int_log 2 n - 2 ^ (int_log 2 n + 1) + 1 + n by algebra.
have -> :
  n %/ 2 * int_log 2 n - 2 ^ int_log 2 n + 1 +
  (n %%/ 2 * int_log 2 (n %%/ 2) -
   2 ^ (int_log 2 (n %%/ 2) + 1) + n %%/ 2 + 1) +
  n - 1 =
  n %/ 2 * int_log 2 n - 2 ^ int_log 2 n +
  n %%/ 2 * int_log 2 (n %%/ 2) - 2 ^ (int_log 2 (n %%/ 2) + 1)
  + n %%/ 2 + 1 + n by algebra.
rewrite -subr_eq addrK.
rewrite -subr_eq addrK.
have [lt | eq] :
  n < 2 ^ (int_log 2 n + 1) - 1 \/ n = 2 ^ (int_log 2 n + 1) - 1.
  smt(int_log_ub_lt).
rewrite int_log2_divup_min1 //=.
have -> :
  n %/ 2 * int_log 2 n - 2 ^ int_log 2 n +
  n %%/ 2 * (int_log 2 n - 1) - 2 ^ int_log 2 n + n %%/ 2 =
  n %/ 2 * int_log 2 n + n %%/ 2 * int_log 2 n -
  (2 ^ int_log 2 n + 2 ^ int_log 2 n) by algebra.
by rewrite -mul2l -exprS 1:int_log_ge0 // -subr_eq addrK -mulrDl
           -div2_plus_div2up_eq.
rewrite int_log2_divup_eq //.
have -> :
  n %/ 2 * int_log 2 n - 2 ^ int_log 2 n + n %%/ 2 * int_log 2 n -
  2 ^ (int_log 2 n + 1) + n %%/ 2 =
  (n %/ 2 + n %%/ 2) * int_log 2 n + n %%/ 2
  - 2 ^ int_log 2 n - 2 ^ (int_log 2 n + 1) by algebra.
rewrite -subr_eq addrK -div2_plus_div2up_eq -addrA.
have -> // : n %%/ 2 - 2 ^ int_log 2 n = 0.
rewrite subr_eq /= int_div_up2_odd 1:eq /=.
by rewrite odd_iff_plus1_even /= exprS 1:int_log_ge0 // dvdz_mulr.
by rewrite {1}eq /= exprS 1:int_log_ge0 // mulKz.
qed.

(* for some small number of values of n, wc n = n * int_log 2 n, but
   for most values of n, wc n < n * int_log 2 n

   according to an OCaml program we wrote (see
   ocaml-code/bounds-compare.ml), there is a periodicity to the
   above which presumably could be proved using lemma wc_eq

   e.g., when n = 4095, both are 45045; but when n = 4096 there is a
   gap of 4095 that becomes one smaller at each increment of n until
   the gap becomes 0 again when n = 8192 and both are 98292 *)

lemma wc_le (n : int) :
  1 <= n => wc n <= n * int_log 2 n.
proof.
move => ge1_n.
rewrite wc_eq // ler_subl_addr ler_addl.
smt(int_log_ub_lt).
qed.

(* we define the merge operator and prove properies of it *)

op merge (e : 'a -> 'a -> bool, xs ys : 'a list) : 'a list =
  with xs = [],      ys = []      => []
  with xs = [],      ys = _ :: _  => ys
  with xs = _ :: _,  ys = []      => xs
  with xs = u :: us, ys = v :: vs =>
    if e u v
    then u :: merge e us ys
    else v :: merge e xs vs.

lemma merge_nil_r (e : 'a -> 'a -> bool, xs : 'a list) :
  merge e xs [] = xs.
proof.
by case xs.
qed.

lemma merge_nil_l (e : 'a -> 'a -> bool, xs : 'a list) :
  merge e [] xs = xs.
proof.
by case xs.
qed.

lemma size_merge (e : 'a -> 'a -> bool, xs ys : 'a list) :
  size (merge e xs ys) = size xs + size ys.
proof.
move : ys.
elim xs => [ys /= |].
by rewrite merge_nil_l.
move => x xs IHouter ys.
elim ys => [// | y ys IHinner /=].
case (e x y) => [e_x_y | not_e_x_y].
rewrite IHouter /=; algebra.
rewrite IHinner /=; algebra.
qed.

lemma cmp_head_merge (cmp : 'a -> 'a -> bool, n : 'a, xs ys : 'a list) :
  cmp n (head n xs) => cmp n (head n ys) =>
  cmp n (head n (merge cmp xs ys)).
proof.
case xs => [| u us].
by case ys.
case ys => [// | v vs /=].
by case (cmp u v).
qed.

lemma merge_sorted (e : 'a -> 'a -> bool, xs ys : 'a list) :
  (forall (a : 'a), e a a) =>
  (forall (a b : 'a), e a b \/ e b a) =>
  sorted e xs => sorted e ys =>
  sorted e (merge e xs ys).
proof.
move => refl_e tot_e; move : ys.
elim xs => [| u us IH_outer].
by case.
elim => [// | v vs /= IH_inner path_u_us path_v_vs].
case (e u v) => [e_u_v | not_e_u_v].
rewrite (pathP u); right; split => [| /=].
by rewrite cmp_head_merge cmp_head_path_same_def.
by rewrite IH_outer (path_sorted _ u).
rewrite (pathP v); right; split => [| /=].
rewrite cmp_head_merge cmp_head_path_same_def //= path_u_us /= 1:/#.
by rewrite IH_inner // (path_sorted _ v).
qed.

lemma perm_eq_merge (e : 'a -> 'a -> bool, xs ys : 'a list) :
  perm_eq (merge e xs ys) (xs ++ ys).
proof.
move : ys.
elim xs => [ys /= | x xs IH_outer ys].
rewrite merge_nil_l perm_eq_refl.
elim ys => [/= | v vs IH_inner /=].
rewrite cats0 perm_eq_refl.
case (e x v) => [e_x_v | not_e_x_v].
rewrite -cat1s -(cat1s _ (xs ++ v :: vs)) perm_cat2l IH_outer.
rewrite -cat1s (perm_eq_trans ([v] ++ (x :: xs ++ vs)))
        1:perm_cat2l 1:IH_inner.
have -> : [v] ++ (x :: xs ++ vs) = [v] ++ [x] ++ (xs ++ vs) by smt(catA).
have -> : x :: (xs ++ v :: vs) = [x] ++ xs ++ ([v] ++ vs) by smt(catA).
rewrite perm_catCAl -!catA perm_cat2l !catA.
rewrite perm_catCAl -!catA perm_cat2l perm_eq_refl.
qed.

lemma perm_eq_merge_perms (e : 'a -> 'a -> bool, xs ys us vs : 'a list) :
  perm_eq us xs => perm_eq vs ys =>
  perm_eq (merge e us vs) (xs ++ ys).
proof.
move => pe_us_xs pe_vs_ys.
rewrite (perm_eq_trans (us ++ vs)) 1:perm_eq_merge.
by rewrite (perm_eq_trans (xs ++ vs)) 1:perm_cat2r // perm_cat2l.
qed.

lemma merge_sort_cat (e : 'a -> 'a -> bool, xs ys : 'a list) :
  (forall (x : 'a), e x x) =>
  (forall (y x z : 'a), e x y => e y z => e x z) =>
  (forall (x y : 'a), e x y => e y x => x = y) =>
  (forall (x y : 'a), e x y \/ e y x) =>
  merge e (sort e xs) (sort e ys) = sort e (xs ++ ys).
proof.
move => refl_e trans_e antisym_e tot_e.
have -> :
  merge e (sort e xs) (sort e ys) =
  sort e (merge e (sort e xs) (sort e ys)).
  by rewrite eq_sym sort_id // merge_sorted // sort_sorted.
rewrite -perm_sortP // perm_eq_merge_perms 2!perm_sort.
qed.

(* the state of the merge sort algorithm is a term in a simple
   functional programming language

   below we will specify, as a function of a comparison operation, the
   list of integers that is represented by a term (i.e., the meaning
   of the term)

   we will also give a single-step operational semantics for terms,
   which periodically blocks, waiting for the result of a comparision

   in the operational semantics, we'll start with Sort range_len, and
   end with List xs where xs is the permutation of range_len
   consistent with the comparison operation *)

type term = [
  | Sort  of int list
  | List  of int list
  | Cons  of int & term
  | Merge of term & term
  | Cond  of int & int & int list & int list
].

op is_sort (t : term) : bool =
  with t = Sort _       => true
  with t = List _       => false
  with t = Cons _ _     => false
  with t = Merge _ _    => false
  with t = Cond _ _ _ _ => false.

op of_sort (t : term) : int list =
  with t = Sort xs      => xs
  with t = List _       => []  (* in the other cases, we don't *)
  with t = Cons _ _     => []  (* care what is returned *)
  with t = Merge _ _    => []
  with t = Cond _ _ _ _ => [].

lemma is_sort (t : term) :
  is_sort t => t = Sort (of_sort t).
proof. by case t. qed.

op is_list (t : term) : bool =
  with t = Sort _       => false
  with t = List _       => true
  with t = Cons _ _     => false
  with t = Merge _ _    => false
  with t = Cond _ _ _ _ => false.

op of_list (t : term) : int list =
  with t = Sort _       => []
  with t = List xs      => xs
  with t = Cons _ _     => []
  with t = Merge _ _    => []
  with t = Cond _ _ _ _ => [].

lemma is_list (t : term) :
  is_list t => t = List (of_list t).
proof. by case t. qed.

op is_cons (t : term) : bool =
  with t = Sort _       => false
  with t = List _       => false
  with t = Cons _ _     => true
  with t = Merge _ _    => false
  with t = Cond _ _ _ _ => false.

op of_cons (t : term) : int * term =
  with t = Sort _       => (0, List [])
  with t = List _       => (0, List [])
  with t = Cons i u     => (i, u)
  with t = Merge _ _    => (0, List [])
  with t = Cond _ _ _ _ => (0, List []).

lemma is_cons (t : term) :
  is_cons t => t = Cons (of_cons t).`1 (of_cons t).`2.
proof. by case t. qed.

op is_merge (t : term) : bool =
  with t = Sort _       => false
  with t = List _       => false
  with t = Cons _ _     => false
  with t = Merge _ _    => true
  with t = Cond _ _ _ _ => false.

op of_merge (t : term) : term * term =
  with t = Sort _       => (List [], List [])
  with t = List _       => (List [], List [])
  with t = Cons _ _     => (List [], List [])
  with t = Merge u v    => (u, v)
  with t = Cond _ _ _ _ => (List [], List []).

lemma is_merge (t : term) :
  is_merge t => t = Merge (of_merge t).`1 (of_merge t).`2.
proof. by case t. qed.

op is_cond (t : term) : bool =
  with t = Sort _       => false
  with t = List _       => false
  with t = Cons _ _     => false
  with t = Merge _ _    => false
  with t = Cond _ _ _ _ => true.

op of_cond (t : term) : int * int * int list * int list =
  with t = Sort _         => (0, 0, [], [])
  with t = List _         => (0, 0, [], [])
  with t = Cons _ _       => (0, 0, [], [])
  with t = Merge _ _      => (0, 0, [], [])
  with t = Cond i j us vs => (i, j, us, vs).

lemma is_cond (t : term) :
  is_cond t => t =
  Cond (of_cond t).`1 (of_cond t).`2 (of_cond t).`3 (of_cond t).`4.
proof. by case t. qed.

(* the list represented by a term, relative to a comparison
   relation *)

op repr (cmp : int -> int -> bool, t : term) : int list =
  with t = Sort xs        => sort cmp xs
  with t = List xs        => xs
  with t = Cons i u       => i :: repr cmp u
  with t = Merge u v      => merge cmp (repr cmp u) (repr cmp v)
  with t = Cond i j us vs =>
    if cmp i j
    then i :: merge cmp us        (j :: vs)
    else j :: merge cmp (i :: us) vs.

(* we are going to define which terms are "proper", i.e., well-formed;
   to do this, we need some auxiliary definitions, about which we
   prove some lemmas *)

op proper_list0 (xs : int list) : bool =  (* may be empty *)
  uniq xs /\ all (mem range_len) xs.

op proper_list (xs : int list) : bool =
  xs <> [] /\ uniq xs /\ all (mem range_len) xs.

lemma proper_list0_from_proper_list (xs : int list) :
  proper_list xs => proper_list0 xs.
proof.
by rewrite /proper_list /proper_list0.
qed.

lemma cat_eq_nil_iff (xs ys : 'a list) :
  xs ++ ys = [] <=> xs = [] /\ ys = [].
proof. by case xs. qed.

lemma proper_list_cat_iff (xs ys : int list) :
  proper_list (xs ++ ys) <=>
  xs = [] /\ proper_list ys \/
  ys = [] /\ proper_list xs \/
  proper_list xs /\ proper_list ys /\ ! has (mem ys) xs.
proof.
rewrite /proper_list all_cat cat_uniq has_sym.
split =>
  [[#] xs_cat_ys_ne_nil -> -> -> -> -> /# |
   [[#] -> /= -> -> -> // |
    [[#] -> /= xs_ne_nil -> -> |
     [#] xs_ne_nil -> -> ys_ne_nil -> -> -> /=]
   ]
  ].
by rewrite cats0 in_nilE has_pred0.
by rewrite cat_eq_nil_iff negb_and xs_ne_nil.
qed.

lemma proper_list_cat_both_ne_iff (xs ys : int list) :
  xs <> [] => ys <> [] =>
  proper_list (xs ++ ys) <=>
  proper_list xs /\ proper_list ys /\ ! has (mem ys) xs.
proof.
smt(proper_list_cat_iff).
qed.

lemma proper_list_cat_if_both_proper (xs ys : int list) :
  proper_list xs => proper_list ys => ! has (mem xs) ys =>
  proper_list (xs ++ ys).
proof.
smt(proper_list_cat_both_ne_iff has_sym).
qed.

lemma proper_list0_cons_iff (i : int, xs : int list) :
  proper_list0 (i :: xs) <=>
  mem range_len i /\ ! mem xs i /\ proper_list0 xs.
proof.
rewrite /proper_list0 /=.
split => [[#] -> -> -> -> // | [#] -> -> -> -> //].
qed.

lemma proper_list0_cons (i : int, xs : int list) :
  proper_list0 xs => mem range_len i => ! mem xs i =>
  proper_list0 (i :: xs).
proof.
smt(proper_list0_cons_iff).
qed.

lemma proper_list_cons_iff (i : int, xs : int list) :
  proper_list (i :: xs) <=>
  mem range_len i /\ ! mem xs i /\ uniq xs /\ all (mem range_len) xs.
proof.
rewrite /proper_list /=.
split => [[#] -> -> -> -> // | [#] -> -> -> -> //].
qed.

lemma proper_list_cons (i : int, xs : int list) :
  proper_list xs => mem range_len i => ! mem xs i =>
  proper_list (i :: xs).
proof.
smt(proper_list_cons_iff).
qed.

lemma proper_list_range_len :
  proper_list range_len.
proof.
rewrite /proper_list.
split; first by rewrite -size_eq0 size_range_len gtr_eqF 1:ltzE /= 1:ge1_len.
by rewrite uniq_range_len /= allP.
qed.

(* elems t is the set of integers appearing in t *)

op elems (t : term) : int fset =
  with t = Sort xs        => oflist xs
  with t = List xs        => oflist xs
  with t = Cons i u       => fset1 i `|` elems u
  with t = Merge u v      => elems u `|` elems v
  with t = Cond i j us vs => fset1 i `|` fset1 j  `|` oflist us `|` oflist vs.

lemma is_list_elems (t : term) :
  is_list t => oflist (of_list t) = elems t.
proof. by case t. qed.

(* we will often only be interested in terms that are "proper" (well
   formed) in the following sense

   the clause for Merge is written to enforce that the operational
   semantics evaluates in a left-to-right order *)

op proper (t : term) : bool =
  with t = Sort xs        => proper_list xs
  with t = List xs        => proper_list0 xs
  with t = Cons i u       =>
    mem range_len i /\ proper u /\ ! mem (elems u) i
  with t = Merge u v      =>
    proper u /\ proper v /\ (! is_sort v => is_list u) /\
    disjoint (elems u) (elems v) /\ elems u `|` elems v <> fset0
  with t = Cond i j us vs =>
    proper_list0 (i :: us) /\ proper_list0 (j :: vs) /\
    ! has (mem (i :: us)) (j :: vs).

lemma is_list_proper_iff (t : term) :
  is_list t => proper t <=> proper_list0 (of_list t).
proof. by case t. qed.

lemma is_list_mem_iff (i : int, t : term) :
  is_list t => i \in of_list t <=> i \in elems t.
proof.
case t => //= xs.
by rewrite mem_oflist.
qed.

lemma proper_start :
  proper (Sort range_len).
proof.
rewrite /= /proper_list /range_len.
split; first by rewrite range_ltn 1:ltzE /= 1:ge1_len.
split; first rewrite range_uniq.
by rewrite allP.
qed.

(* our operational semantics has two parts, the first part
   being a step operator *)

type step = [  (* result of call to step on term t *)
  | Done                  (* t is fully evaluated: List ... *)
  | Compare of int & int  (* t's evaluation needs answer to comparison
                             request i, j: is element at index i less
                             than element at index j *)
  | Worked  of term       (* the step succeeded, producing term *)
].

op is_compare (s : step) : bool =
  with s = Done        => false
  with s = Compare i j => true
  with s = Worked t    => false.

op of_compare (s : step) : int * int =
  with s = Done        => (0, 0)
  with s = Compare i j => (i, j)
  with s = Worked t    => (0, 0).

op is_worked (s : step) : bool =
  with s = Done        => false
  with s = Compare i j => false
  with s = Worked t    => true.

op of_worked (s : step) : term =
  with s = Done        => List [1]
  with s = Compare i j => List [1]
  with s = Worked t    => t.

lemma is_compare_iff (s : step) :
  is_compare s <=> s <> Done /\ ! is_worked s.
proof. by case s. qed.

lemma is_worked_iff (s : step) :
  is_worked s <=> s <> Done /\ ! is_compare s.
proof. by case s. qed.

lemma eq_done_iff (s : step) :
  s = Done <=> ! is_compare s /\ ! is_worked s.
proof. by case s. qed.

op step (t : term) : step =
  with t = Sort xs      =>
    if size xs <= 1  (* will never be 0 *)
    then Worked (List xs)
    else let mid = size xs %/ 2 in
         Worked
         (Merge
          (Sort (take mid xs))   (* size: size xs %/ 2 *)
          (Sort (drop mid xs)))  (* size: size xs %%/ 2 *)
  with t = List xs      => Done
  with t = Cons n u     =>
    let u' = step u in
    if is_worked u'
      then Worked (Cons n (of_worked u'))
    else if is_compare u'
      then u'
    else (* is_list u *)
         Worked (List (n :: of_list u))
  with t = Merge u v    =>
    let u' = step u in
    if is_worked u'
      then Worked (Merge (of_worked u') v)
    else if is_compare u'
      then u'
    else let v' = step v in
         if is_worked v'
           then Worked (Merge u (of_worked v'))
         else if is_compare v'
           then v'
         else (* is_list u /\ is_list v *)
              if of_list u = []
                then Worked v
              else if of_list v = []
                then Worked u
              else let i  = head 0 (of_list u) in
                   let ms = behead (of_list u) in
                   let j  = head 0 (of_list v) in
                   let ns = behead (of_list v) in
                   Worked (Cond i j ms ns)
  with t = Cond i j u v => Compare i j.

lemma step_done_iff (t : term) :
  step t = Done <=> is_list t.
proof.
elim t => // /#.
qed.

(* a "general" lemma, with specializations to follow *)

lemma is_worked_proper_step_gen (t : term) :
  proper t => is_worked (step t) =>
  elems (of_worked (step t)) = elems t /\ elems t <> fset0 /\
  proper (of_worked (step t)).
proof.
elim t => //.
move => xs /=.
case (size xs <= 1) => [ge1_size_xs | gt1_size_xs pl_xs _].
rewrite /proper_list /proper_list0 => [#] xs_nonnil -> -> _ /=.
by rewrite oflist_eq_fset0_iff.
rewrite lerNgt /= in gt1_size_xs.
have xs_eq := cat_take_drop (size xs %/ 2) xs.
split; first by rewrite -{5}xs_eq oflist_cat.
have [plc_xs_first _] :=
    proper_list_cat_both_ne_iff
    (take (size xs %/ 2) xs) (drop (size xs %/ 2) xs)
     _ _ => //.
  rewrite -size_eq0 size_take /#.
  rewrite -size_eq0 size_drop /#.
split; first rewrite oflist_eq_fset0_iff /#.
have plc_xs := plc_xs_first _. by rewrite xs_eq.
split; first by elim plc_xs.
split => [| /=]; first by elim plc_xs.
split.
rewrite disjointP => x.
rewrite 2!mem_oflist.
smt(hasPn).
rewrite -oflist_cat oflist_eq_fset0_iff /#.
move => i t IH /= [i_in_range [prop_t not_i_in_elems_t]].
case (is_worked (step t)) => [is_wkd_step_t | not_is_wkd_step_t].
have [elems_eq [elems_t_ne_fset0 prop_of_wrkd_step_t]] _ := IH _ _ => //.
rewrite elems_eq /= prop_of_wrkd_step_t.
split => [| //].
by rewrite fset1_union_any_ne_fset0.
case (is_compare (step t)) =>
  [is_cmp_step_t is_wkd_step_t | not_is_cmp_step_t _].
smt(eq_done_iff).
have is_list_t : is_list t by rewrite -step_done_iff eq_done_iff.
split; first by rewrite oflist_cons is_list_elems.
split; first by rewrite fset1_union_any_ne_fset0.
rewrite proper_list0_cons //.
by rewrite -is_list_proper_iff.
by rewrite is_list_mem_iff.
move => t u IHt IHu.
rewrite /= =>
  [#] prop_t prop_u kind_imp disj_t_u elems_t_union_elems_u_ne_fset0.
case (is_worked (step t)) => [is_wkd_step_t _ | not_is_wkd_step_t].
have [elems_eq [elems_t_ne_fset0 prop_of_wrkd_step_t]] := IHt _ _ => //.
rewrite elems_eq /= prop_of_wrkd_step_t prop_u /=.
split; first by rewrite union_eq_fset0_iff negb_and elems_t_ne_fset0.
split => [is_list_u | //].
smt(step_done_iff).
case (is_compare (step t)) => [/# | not_is_cmp_step_t].
case (is_worked (step u)) => [is_wkd_step_u _ | not_is_wkd_step_u].
have [elems_eq [elems_u_ne_fset0 prop_of_wrkd_step_u]] := IHu _ _ => //.
rewrite elems_eq /= prop_of_wrkd_step_u prop_t /=.
split; first by rewrite union_eq_fset0_iff negb_and elems_u_ne_fset0.
split => [is_list_of_wkd_step_u | //].
by rewrite -step_done_iff eq_done_iff.
case (is_compare (step u)) => [/# | not_is_cmp_step_u].
case (of_list t = []) => [A _ | of_list_t_ne_nil].
rewrite -{1}(is_list_elems t) 1:-step_done_iff 1:eq_done_iff //.
have -> : oflist (of_list t) = fset0 by rewrite oflist_eq_fset0_iff.
by rewrite fset0U.
case (of_list u = []) => [of_list_u_eq_nil _ | of_list_u_ne_nil _].
rewrite -(is_list_elems t) 1:-step_done_iff 1:eq_done_iff //.
rewrite -(is_list_elems u) 1:-step_done_iff 1:eq_done_iff //.
have -> : oflist (of_list u) = fset0 by rewrite oflist_eq_fset0_iff.
by rewrite fsetU0 oflist_eq_fset0_iff.
have is_list_t : is_list t by rewrite -step_done_iff eq_done_iff.
have is_list_u : is_list u by rewrite -step_done_iff eq_done_iff.
split.
rewrite -(is_list_elems t) // -(is_list_elems u) //.
rewrite -{3}(head_behead (of_list t) 0) //.
rewrite -{3}(head_behead (of_list u) 0) //.
rewrite 2!oflist_cons.
smt(fsetUC fsetUA).
have proper_list0_of_list_t :
  proper_list0 (of_list t) by rewrite -is_list_proper_iff.
have proper_list0_of_list_u :
  proper_list0 (of_list u) by rewrite -is_list_proper_iff.
have of_list_t_eq := head_behead (of_list t) 0 _ => //.
have of_list_u_eq := head_behead (of_list u) 0 _ => //.
split; first smt().
split; first smt().
rewrite negb_or.
have of_list_t_not_in_of_list_u : ! has (mem (of_list u)) (of_list t).
  move : disj_t_u.
  rewrite disjointP -is_list_elems // -is_list_elems // => disj'_t_u.
  rewrite hasPn => x.
  rewrite -2!mem_oflist // => x_in_of_list_t.
  by rewrite disj'_t_u.
have of_list_u_not_in_of_list_t : ! has (mem (of_list t)) (of_list u).
  smt(has_sym).
split; first by rewrite of_list_u_eq.
split; rewrite of_list_t_eq; smt(hasPn).
qed.

lemma is_worked_proper_step (t : term) :
  proper t => is_worked (step t) => proper (of_worked (step t)).
proof. smt(is_worked_proper_step_gen). qed.

lemma is_worked_proper_step_elems_eq (t : term) :
  proper t => is_worked (step t) =>
  elems (of_worked (step t)) = elems t.
proof. smt(is_worked_proper_step_gen). qed.

lemma is_worked_proper_step_elems_ne_fset0 (t : term) :
  proper t => is_worked (step t) => elems (of_worked (step t)) <> fset0.
proof. smt(is_worked_proper_step_gen). qed.

lemma is_compare_proper_step_range (t : term) :
  proper t => is_compare (step t) =>
  0 <= (of_compare (step t)).`1 < len /\
  0 <= (of_compare (step t)).`2 < len.
proof.
elim t => //.
move => xs /=; by case (size xs <= 1).
move => i t IHt /= [#] _ prop_t _.
case (is_worked (step t)) => [// | not_is_wkd_step_t].
case (is_compare (step t)) => [is_cmp_step_t _ /# | //].
move => t u IHt IHu /= [#] prop_t prop_u _ _ _.
case (is_worked (step t)) => [// | not_is_wkd_step_t].
case (is_compare (step t)) => [is_cmp_step_t _ /# | not_is_cmp_step_t].
case (is_worked (step u)) => [// | not_is_wkd_step_u].
case (is_compare (step u)) => [is_cmp_step_t _ /# | not_is_cmp_step_u].
case (of_list t = []) => [// | _].
by case (of_list u = []).
move => i j us vs /=.
rewrite /proper_list0 /=.
smt(in_range_len).
qed.

lemma is_compare_proper_step_range1 (t : term) :
  proper t => is_compare (step t) =>
  0 <= (of_compare (step t)).`1 < len.
proof. smt(is_compare_proper_step_range). qed.

lemma is_compare_proper_step_range2 (t : term) :
  proper t => is_compare (step t) =>
  0 <= (of_compare (step t)).`2 < len.
proof. smt(is_compare_proper_step_range). qed.

(* the size of repr of a term, uniform for all comparision
   relations *)

op size_term (t : term) : int =
  with t = Sort xs        => size xs
  with t = List xs        => size xs
  with t = Cons i u       => 1 + size_term u
  with t = Merge u v      => size_term u + size_term v
  with t = Cond i j us vs => 2 + size us + size vs.

lemma size_term_ge0 (t : term) :
  0 <= size_term t.
proof.
elim t; smt(size_ge0).
qed.

lemma size_term_eq_card_elems (t : term) :
  proper t => size_term t = card (elems t).
proof.
elim t.
move => xs /=.
rewrite /proper_list => [#] _ uniq_xs _.
by rewrite uniq_card_oflist.
move => xs /=.
rewrite /proper_list0 => [[uniq_xs _]].
by rewrite uniq_card_oflist.
move => i t IH /= [#] _ prop_t i_notin_elems_t.
by rewrite fsetUC fcardUindep1 // addrC IH.
move => t u IHt IHu /= [#] prop_t prop_u _ disj_t_u _.
by rewrite fcardUI_indep // IHt // IHu.
move => i j xs ys /=.
rewrite /proper_list0 /= =>
  [#] i_notin_xs uniq_xs _ _ j_notin_ys uniq_ys _ _.
rewrite !negb_or => [#] ne_j_i j_notin_xs ys_notin_i_cons_xs.
rewrite fcardUI_indep.
rewrite disjointP => x.
rewrite !in_fsetU !in_fset1 !mem_oflist => [[[-> | //] |]].
smt(hasPn). smt(hasPn).
rewrite fcardUI_indep.
rewrite disjointP => x.
rewrite !in_fsetU !in_fset1 !mem_oflist => [[-> // | -> //]].
rewrite fcardUI_indep.
rewrite disjointP => x.
rewrite !in_fset1 => ->.
by rewrite eq_sym ne_j_i.
rewrite 2!fcard1.
by rewrite uniq_card_oflist // uniq_card_oflist.
qed.

lemma size_term_ge1_when_proper_elems_ne_fset0 (t : term) :
  proper t => elems t <> fset0 =>
  1 <= size_term t.
proof.
move => prop_t elems_t_ne.
rewrite size_term_eq_card_elems //.
smt(fcard_ge0 fcard_eq0).
qed.

lemma size_term_eq_size_repr (cmp : int -> int -> bool, t : term) :
  size_term t = size (repr cmp t).
proof.
elim t => //.
move => xs /=.
by rewrite size_sort.
move => i t IH /=.
by rewrite IH.
move => t u IHt IHu /=.
by rewrite IHt IHu size_merge.
move => i j us vs /=.
case (cmp i j) => [cmp_i_j | not_cmp_i_j].
rewrite size_merge /=; algebra.
rewrite size_merge /=; algebra.
qed.

lemma size_term_step (t : term) :
  proper t => is_worked (step t) =>
  size_term (of_worked (step t)) = size_term t.
proof.
move => prop_t is_wkd_step_t.
rewrite size_term_eq_card_elems 1:is_worked_proper_step //.
by rewrite size_term_eq_card_elems // is_worked_proper_step_elems_eq.
qed.

lemma repr_start (cmp : int -> int -> bool) :
  repr cmp (Sort range_len) = sort cmp range_len.
proof. trivial. qed.

lemma repr_done (cmp : int -> int -> bool, t : term) :
  is_list t => repr cmp t = of_list t.
proof.
move => is_list_t.
by rewrite {1}is_list.
qed.

lemma is_worked_repr_step (cmp : int -> int -> bool, t : term) :
  (forall (x : int), cmp x x) =>
  (forall (y x z : int), cmp x y => cmp y z => cmp x z) =>
  (forall (x y : int), cmp x y => cmp y x => x = y) =>
  (forall (x y : int), cmp x y \/ cmp y x) =>
  proper t => is_worked (step t) =>
  repr cmp (of_worked (step t)) = repr cmp t.
proof.
move => refl_e trans_e antisym_e tot_e.
elim t => //.
move => xs /= _.
case (size xs <= 1) => [le1_size_xs _ | gt1_size_xs _].
have [eq0_size_xs | eq1_size_xs] :
  size xs = 0 \/ size xs = 1 by smt(size_ge0).
rewrite size_eq0 in eq0_size_xs.
by rewrite eq0_size_xs /sort.
rewrite size_eq1 in eq1_size_xs.
elim eq1_size_xs => x ->; by rewrite /sort.
rewrite lerNgt /= in gt1_size_xs.
have {5}<- := cat_take_drop (size xs %/ 2) xs.
by rewrite merge_sort_cat.
move => i t IH /= [#] _ prop_t _.
case (is_worked (step t)) => [is_wkd_step_t _ | not_is_wkd_step_t].
by rewrite IH.
case (is_compare (step t)) => [| not_is_cmp_step_t _].
smt(is_worked_iff).
congr.
have is_list_t : is_list t by rewrite -step_done_iff eq_done_iff.
by rewrite is_list.
move => t u IHt IHu /= [#] prop_t prop_u _ _.
case (is_worked (step t)) => [is_wkd_step_t _ | not_is_wkd_step_t].
by rewrite IHt.
case (is_compare (step t)) => [| not_is_cmp_step_t].
by rewrite is_compare_iff.
case (is_worked (step u)) => [is_wkd_step_u _ | not_is_wkd_step_u].
by rewrite IHu.
case (is_compare (step u)) => [| not_is_cmp_step_u].
smt(is_compare_iff).
have is_list_t : is_list t by rewrite -step_done_iff eq_done_iff.
have is_list_u : is_list u by rewrite -step_done_iff eq_done_iff.
case (of_list t = []) => [of_list_t_eq_nil _ | of_list_t_ne_nil].
by rewrite (is_list t) //= of_list_t_eq_nil merge_nil_l.
case (of_list u = []) => [of_list_u_eq_nil | of_list_u_ne_nil _].
by rewrite (is_list u) //= of_list_u_eq_nil merge_nil_r.
have -> : repr cmp t = of_list t by rewrite is_list.
have -> : repr cmp u = of_list u by rewrite is_list.
have of_list_t_eq := head_behead (of_list t) 0 _ => //.
have of_list_u_eq := head_behead (of_list u) 0 _ => //.
case (cmp (head 0 (of_list t)) (head 0 (of_list u))) =>
  [cmp_t_u | not_cmp_t_u].
by rewrite -{3}of_list_t_eq -{3}of_list_u_eq /= cmp_t_u.
by rewrite -{3}of_list_t_eq -{3}of_list_u_eq /= not_cmp_t_u.
qed.

lemma is_worked_repr_step_cmp_of_rel (inps : inp list, t : term) :
  total_ordering inps => proper t => is_worked (step t) =>
  repr (cmp_of_rel inps) (of_worked (step t)) =
  repr (cmp_of_rel inps) t.
proof.
move => to_inps prop_t is_wkd_step_t.
rewrite is_worked_repr_step //.
move => x.
by rewrite cmp_tot_ord_refl cmp_tot_ord_of_tot_ord.
move => y x z cor_x_y cor_y_z.
by rewrite (cmp_tot_ord_trans inps y x z) 1:cmp_tot_ord_of_tot_ord.
move => x y cor_x_y cor_y_x.
by rewrite (cmp_tot_ord_antisym inps x y) 1:cmp_tot_ord_of_tot_ord.
move => x y.
by rewrite cmp_tot_ord_total cmp_tot_ord_of_tot_ord.
qed.

(* supporting lemma for termination metric for step *)

lemma square_divide_lt (n : int) :
  2 <= n =>
  1 + (n %/ 2) ^ 2 + (n %%/ 2) ^ 2 < n ^ 2.
proof.
move => ge2_n.
have -> : n ^ 2 = (n %/ 2 + n %%/ 2) ^ 2 by rewrite {1}div2_plus_div2up_eq.
rewrite 3!expr2.
have -> :
  1 + n %/ 2 * (n %/ 2) + n %%/ 2 * (n %%/ 2) =
  (n %/ 2 * (n %/ 2) + n %%/ 2 * (n %%/ 2)) + 1.
  algebra.
have -> :
  (n %/ 2 + n %%/ 2) * (n %/ 2 + n %%/ 2) =
  ((n %/ 2) * (n %/ 2) + (n %%/ 2) * (n %%/ 2)) +
  ((n %/ 2) * (n %%/ 2) + (n %%/ 2) * (n %/ 2)).
  algebra.
have ge1_n_div2 : 1 <= n %/ 2 by smt().
have ge1_n_div2up : 1 <= n %%/ 2 by smt(int_div2_up_ge1_implies_ge1).
rewrite ltz_add2l /#.
qed.

(* termination metric for step *)

op metric (t : term) : int =
  with t = Sort xs        => size xs ^ 2
  with t = List xs        => 0
  with t = Cons i u       => metric u + 1
  with t = Merge u v      => 1 + metric u + metric v
  with t = Cond i j us vs => 0.

lemma metric_ge0 (t : term) :
  0 <= metric t.
proof.
elim t => //.
move => xs /=; smt(size_ge0 expr2).
smt(). smt().
qed.

lemma metric_step (t : term) :
  proper t => is_worked (step t) =>
  metric (of_worked (step t)) < metric t.
proof.
elim t => //.
move => xs /= pl_xs.
case (size xs <= 1) => [le1_size_xs _ | gt1_size_xs _].
have -> : size xs = 1 by smt(size_ge0 size_eq0).
by rewrite expr2.
have size_xs_eq := div2_plus_div2up_eq (size xs).
have ge0_size_xs_int_div_up2 : 1 <= size xs %%/ 2.
  smt(int_div2_up_ge1_implies_ge1).
have -> : size (take (size xs %/ 2) xs) = size xs %/ 2.
  rewrite size_take /#.
have -> : size (drop (size xs %/ 2) xs) = size xs %%/ 2.
  rewrite size_drop /#.
rewrite square_divide_lt /#.
trivial.
move => i xs /= IH [#] _ prop_t _.
case (is_worked (step xs)) => [is_wkd_step_xs _ | not_is_wkd_step_xs].
by rewrite ltz_add2r IH.
case (is_compare (step xs)) => [/# | not_is_cmp_step_xs _].
smt(metric_ge0).
move => t u IHt IHu /= [#] prop_t prop_u _ _.
case (is_worked (step t)) => [is_wkd_step_t _ | not_is_wkd_step_t].
smt(metric_ge0).
case (is_compare (step t)) => [/# | not_is_cmp_step_t].
case (is_worked (step u)) => [/# | not_is_wkd_step_u].
case (is_compare (step u)) => [/# | not_is_cmp_step_u].
case (of_list t = []) => [_ _ | of_list_t_ne_nil].
smt(metric_ge0).
case (of_list u = []) => [_ _| of_list_u_ne_nil].
smt(metric_ge0).
smt(metric_ge0).
qed.

lemma metric0_no_step (t : term) :
  proper t => metric t = 0 => ! is_worked (step t).
proof.
move => prop_t eq0_metric_t.
case (is_worked (step t)) => [is_wkd_step_t | //].
have := metric_step t _ _ => //.
rewrite eq0_metric_t.
smt(metric_ge0).
qed.

(* the second part of our operational semantics: how we supply the
   boolean answer to a comparison request

   returns Some of term when this succeeds, and None otherwise;
   see below for necessary and sufficient condition for None
   not resulting *)

op answer (t : term, b : bool) : term option =
  with t = Sort xs        => None
  with t = List xs        => None
  with t = Cons n u       =>
    let u' = answer u b in
    if u' = None
    then None
    else Some (Cons n (oget u'))
  with t = Merge u v      =>
    if is_list u
    then let v' = answer v b in
         if v' = None
         then None
         else Some (Merge u (oget v'))
    else let u' = answer u b in
         if u' = None
         then None
         else Some (Merge (oget u') v)
  with t = Cond i j us vs =>
    if b
    then Some (Cons i (Merge (List us)        (List (j :: vs))))
    else Some (Cons j (Merge (List (i :: us)) (List vs))).

(* "general" result - see below for specializations *)

lemma proper_answer_gen (t : term, b : bool) :
  proper t => answer t b <> None =>
  proper (oget (answer t b)) /\ elems (oget (answer t b)) = elems t /\
  elems t <> fset0 /\ (is_list (oget (answer t b)) <=> is_list t).
proof.
elim t => //.
move => i u IH /= [#] i_in_range prop_u i_not_in_elems_u.
case (answer u b = None) => [// | ans_u_b_ne_none _].
rewrite oget_some /= i_in_range /=.
split; first smt().
split; first smt().
by rewrite fset1_union_any_ne_fset0.
move => t u IHt IHu /= [#] prop_t prop_u kind_imp disj_t_u.
case (is_list t) => [is_list_t | not_is_list_t].
case (answer u b = None) => [// | /#].
case (answer t b = None) => [// | /#].
move => i j us vs /=.
rewrite 2!proper_list0_cons_iff =>
  [#] i_in_range i_notin_us pl0_us j_in_range j_notin_vs pl0_vs.
rewrite negb_or /= negb_or => [#].
rewrite eq_sym => ne_i_j j_notin_us vs_notin_i_cons_us.
case b => _ _ /=.
split.
rewrite oflist_cons !in_fsetU in_fset1 proper_list0_cons_iff.
rewrite pl0_us pl0_vs !mem_oflist !negb_or i_in_range j_in_range.
rewrite i_notin_us j_notin_vs ne_i_j /=.
have -> /= : ! i \in vs by smt(hasPn).
split.
rewrite disjointP => x.
rewrite mem_oflist => x_in_us.
rewrite in_fsetU in_fset1 mem_oflist negb_or.
split; smt(hasPn).
rewrite union_eq_fset0_iff negb_and.
right; rewrite union_eq_fset0_iff negb_and.
left; by rewrite fset1_ne_fset0.
split; first rewrite oflist_cons; smt(fsetUC fsetUA).
by rewrite -!fsetUA fset1_union_any_ne_fset0.
rewrite oflist_cons !in_fsetU in_fset1 proper_list0_cons_iff.
rewrite (eq_sym j) pl0_us pl0_vs !mem_oflist !negb_or.
rewrite i_in_range j_in_range i_notin_us j_notin_vs ne_i_j /=.
have -> /= : ! j \in us by smt(hasPn).
split.
split.
rewrite fsetIC disjointP => x.
rewrite mem_oflist => x_in_vs.
rewrite in_fsetU in_fset1 mem_oflist negb_or.
split; smt(hasPn).
rewrite union_eq_fset0_iff negb_and.
left.
rewrite union_eq_fset0_iff negb_and.
left; by rewrite fset1_ne_fset0.
split.
by rewrite -!fsetUA fsetUCA.
by rewrite -!fsetUA fset1_union_any_ne_fset0.
qed.

lemma proper_answer (t : term, b : bool) :
  proper t => answer t b <> None => proper (oget (answer t b)).
proof.
smt(proper_answer_gen).
qed.

lemma proper_answer_elems_eq (t : term, b : bool) :
  proper t => answer t b <> None =>
  elems (oget (answer t b)) = elems t.
proof. smt(proper_answer_gen). qed.

lemma proper_answer_size_term_eq (t : term, b : bool) :
  proper t => answer t b <> None =>
  size_term (oget (answer t b)) = size_term t.
proof.
move => prop_t good_ans_t_b.
rewrite size_term_eq_card_elems 1:proper_answer //.
rewrite size_term_eq_card_elems //.
by rewrite proper_answer_elems_eq.
qed.

lemma proper_answer_elems_ne_fset0 (t : term, b : bool) :
  proper t => answer t b <> None => elems (oget (answer t b)) <> fset0.
proof. smt(proper_answer_gen). qed.

lemma is_compare_step_iff_good_answer (t : term, b : bool) :
  proper t => is_compare (step t) <=> answer t b <> None.
proof.
elim t => //.
smt().
move => i t IH /= [#] _ prop_t _.
case (is_worked (step t)) => [is_wkd_step_t /= | not_is_wkd_step_t].
have -> // : answer t b = None by smt(is_compare_iff).
case (is_compare (step t)) => [/# | not_is_cmp_step_t].
have -> // : answer t b = None.
  have is_list_t : is_list t.
    by rewrite -step_done_iff eq_done_iff.
  by rewrite is_list.
move => t u IHt IHu /= [#] prop_t prop_u _ _.
case (is_worked (step t)) => [is_wkd_step_t /= | not_is_wkd_step_t].
have -> /= : answer t b = None by smt(is_compare_iff).
case (is_list t) => [| //].
smt(step_done_iff).
case (is_compare (step t)) => [is_cmp_step_t | not_is_cmp_step_t].
case (is_list t) => [| not_is_list_t].
smt(step_done_iff).
have -> // : answer t b <> None by smt().
case (is_worked (step u)) => [is_wkd_step_u | not_is_wkd_step_u].
have -> /= : is_list t by rewrite -step_done_iff eq_done_iff.
have -> // : answer u b = None by smt(is_worked_iff).
case (is_compare (step u)) => [is_cmp_step_u | not_is_cmp_step_u].
have -> /= : is_list t by rewrite -step_done_iff eq_done_iff.
have -> // : answer u b <> None by smt().
case (of_list t = []) => [/# | _].
case (of_list u = []) => [/# | _].
have -> /= : is_list t by rewrite -step_done_iff eq_done_iff.
have -> // : answer u b = None by smt().
move => i j us vs /= _.
by case b.
qed.

lemma is_compare_step_answer_repr (cmp : int -> int -> bool, t : term) :
  proper t => is_compare (step t) =>
  repr cmp
  (oget
   (answer t
    (cmp (of_compare (step t)).`1 (of_compare (step t)).`2))) =
  repr cmp t.
proof.
elim t => //.
smt().
move => i t IH /= [#] i_in_range prop_t _.
case (is_worked (step t)) => [// | not_is_wkd_step_t].
case (is_compare (step t)) => [is_cmp_step_t _ | //].
have -> /= :
  answer t (cmp (of_compare (step t)).`1 (of_compare (step t)).`2) <> None.
  smt(is_compare_step_iff_good_answer).
by rewrite IH.
move => t u IHt IHu /= [#] prop_t prop_u _ _.
case (is_worked (step t)) => [// | not_is_wkd_step_t].
case (is_compare (step t)) => [is_cmp_step_t _ | not_is_cmp_step_t].
have -> /= :
  answer t (cmp (of_compare (step t)).`1 (of_compare (step t)).`2) <> None.
  smt(is_compare_step_iff_good_answer).
have -> /= : ! is_list t.
  rewrite -step_done_iff eq_done_iff negb_and /=.
  by left.
by rewrite IHt.
case (is_worked (step u)) => [// | not_is_wkd_step_u].
case (is_compare (step u)) => [is_cmp_step_u _ | not_is_cmp_step_u].
have -> /= :
  answer u (cmp (of_compare (step u)).`1 (of_compare (step u)).`2) <> None.
  smt(is_compare_step_iff_good_answer).
have -> /= :
  answer t (cmp (of_compare (step u)).`1 (of_compare (step u)).`2) = None.
  smt(is_compare_step_iff_good_answer).
have -> /= : is_list t by rewrite -step_done_iff eq_done_iff.
by rewrite IHu.
case (of_list t = []) => [// | _].
by case (of_list u = []).
move => i j us vs /= _.
by case (cmp i j) => [cmp_i_j | not_cmp_i_j].
qed.

(* an upper bound on the number of comparisons/answers it will
   take to turn a term into list *)

op wc_term (t : term) : int =
  with t = Sort xs        => wc (size xs)
  with t = List _         => 0
  with t = Cons _ t       => wc_term t
  with t = Merge t u      =>
    wc_term t + wc_term u + size_term t + size_term u - 1
  with t = Cond i j us vs => size us + size vs + 1.

lemma wc_term_ge0 (t : term) :
  proper t => 0 <= wc_term t.
proof.
elim t => //.
move => xs /= _.
rewrite wc_ge0.
move => i t IHt /= [#] _ prop_t _ /#.
move => t u IHt IHu /= [#] prop_t prop_u _ _.
rewrite union_eq_fset0_iff negb_and =>
  [[elems_t_ne_fset0 | elems_u_ne_fset0]];
smt(size_term_ge1_when_proper_elems_ne_fset0 size_term_ge0).
move => i j us vs /=.
smt(size_ge0).
qed.

lemma wc_term_start :
  wc_term (Sort range_len) = wc len.
proof.
by rewrite /= size_range_len.
qed.

lemma wc_term_list (xs : int list) :
  wc_term (List xs) = 0.
proof. trivial. qed.

(* when we take a step, wc_term never gets bigger (but sometimes gets
   smaller): *)

lemma wc_term_step (t : term) :
  proper t => is_worked (step t) =>
  wc_term (of_worked (step t)) <= wc_term t.
proof.
elim t => //.
move => xs /= prop_t.
case (size xs <= 1) => [le1_size_xs _ | gt1_size_xs _].
by rewrite wc_when_le1.
rewrite lerNgt /= in gt1_size_xs.
have size_xs_eq := div2_plus_div2up_eq (size xs).
have ge0_size_xs_int_div_up2 : 1 <= size xs %%/ 2.
  smt(int_div2_up_ge1_implies_ge1).
have -> : size (take (size xs %/ 2) xs) = size xs %/ 2.
  rewrite size_take /#.
have -> : size (drop (size xs %/ 2) xs) = size xs %%/ 2.
  rewrite size_drop /#.
rewrite (wc_when_ge2 (size xs)) 1:/#.
smt(div2_plus_div2up_eq).
move => i t IH /= [#] _ prop_t _.
case (is_worked (step t)) => [/# | not_is_wkd_step_t].
case (is_compare (step t)) => [/# | not_is_cmp_step_t _].
have is_list_t : is_list t by rewrite -step_done_iff eq_done_iff.
by rewrite is_list.
move =>
  t u IHt IHu /= [#] prop_t prop_u _ _ elems_t_union_elems_u_ne_fset0.
case (is_worked (step t)) => [is_wkd_step_t _ | not_is_wkd_step_t].
smt(size_term_step).
case (is_compare (step t)) => [/# | not_is_cmp_step_t].
case (is_worked (step u)) => [is_wkd_step_t _ | not_is_wkd_step_u].
smt(size_term_step).
case (is_compare (step u)) => [/# | not_is_cmp_step_u].
have is_list_t : is_list t by rewrite -step_done_iff eq_done_iff.
have is_list_u : is_list u by rewrite -step_done_iff eq_done_iff.
case (of_list t = []) => [of_list_t_eqnil _ | of_list_t_nenil].
move : elems_t_union_elems_u_ne_fset0.
rewrite -is_list_elems // -is_list_elems //.
rewrite of_list_t_eqnil -set0E fset0U => oflist_of_list_u_ne_fset0.
rewrite (is_list t) // of_list_t_eqnil /=.
smt(is_list_elems size_term_ge1_when_proper_elems_ne_fset0).
case (of_list u = []) => [of_list_u_eqnil _ | of_list_u_nenil _].
move : elems_t_union_elems_u_ne_fset0.
rewrite -is_list_elems // -is_list_elems //.
rewrite of_list_u_eqnil -set0E fsetU0 => oflist_of_list_u_ne_fset0.
rewrite (is_list u) // of_list_u_eqnil /=.
smt(is_list_elems size_term_ge1_when_proper_elems_ne_fset0).
rewrite (is_list t) // (is_list u) //=.
have <- := head_behead (of_list t) 0 _ => //.
have <- := head_behead (of_list u) 0 _ => //#.
qed.

(* when we answer a comparision request, wc_term always gets strictly
   smaller *)

lemma wc_term_answer (t : term, b : bool) :
  proper t => answer t b <> None =>
  wc_term (oget (answer t b)) < wc_term t.
proof.
elim t => //.
move => i t IHt /= [#] _ prop_t _.
case (answer t b = None) => [// | ans_t_b_not_none _].
by rewrite oget_some /= IHt.
move => t u IHt IHu /= [#] prop_t prop_u _ _ H.
case (is_list t) => [is_list_t | not_is_list_t].
case (answer u b = None) => [// | ans_u_b_not_none _].
rewrite oget_some /= -!addrA ltz_add2l ltr_le_add 1:IHu //.
by rewrite ler_add2l proper_answer_size_term_eq.
case (answer t b = None) => [// | ans_t_b_not_none _].
rewrite oget_some /= -!addrA ltr_le_add 1:IHt //.
by rewrite ler_add2l proper_answer_size_term_eq.
move => i j us vs /= H.
case b => [b_true | b_false] _; rewrite oget_some /= /#.
qed.

(* poten_cmps returns the set of comparison requests that could
   possibly result from t's evaluation *)

op poten_cmps (t : term) : (int * int) fset =
  with t = Sort xs        => product (oflist xs) (oflist xs)
  with t = List _         => fset0
  with t = Cons _ t       => poten_cmps t
  with t = Merge t u      =>
    poten_cmps t `|` poten_cmps u `|` product (elems t) (elems u)
  with t = Cond i j us vs =>
    product (oflist (i :: us)) (oflist (j :: vs)).

lemma poten_cmps_subset (t : term) :
  poten_cmps t \subset product (elems t) (elems t).
proof.
elim t => //.
move => xs /=; by rewrite sub0set.
move => i xs IH /=.
rewrite (subset_trans _ (product (elems xs) (elems xs))) 1:IH => [[a b]].
rewrite !productP !in_fsetU !in_fset1 /#.
move => t u IHt IHu /=.
rewrite subsetP => [[a b]].
smt(productP in_fsetU).
move => i j us vs /=.
rewrite oflist_cons subsetP => [[a b]].
rewrite !productP oflist_cons !in_fsetU !in_fset1 !mem_oflist /#.
qed.

lemma mem_poten_cmps_disjoint (t u : term, p q : int * int) :
  p \in poten_cmps t => q \in poten_cmps u =>
  disjoint (elems t) (elems u) => p <> q.
proof.
move => p_in_pcs_t q_in_pcs_u disj_t_u.
case (p = q) => [eq_p_q | //].
have p1_in_elems_t : p.`1 \in elems t by smt(poten_cmps_subset productP).
have p1_in_elems_u : p.`1 \in elems u by smt(poten_cmps_subset productP).
by rewrite /= -(in_fset0 (p.`1)) -disj_t_u in_fsetI.
qed.

lemma mem_poten_cmps_disjoint_not_elems1 (t u : term, c d : int) :
  (c, d) \in poten_cmps t => disjoint (elems t) (elems u) =>
  ! c \in elems u.
proof.
move => c_d_in_pcs_t disj_t_u.
case (c \in elems u) => [c_in_elems_u | //].
have c_in_elems_t : c \in elems t by smt(poten_cmps_subset productP).
by rewrite /= -(in_fset0 c) -disj_t_u in_fsetI.
qed.

lemma mem_poten_cmps_disjoint_not_elems2 (t u : term, c d : int) :
  (c, d) \in poten_cmps t => disjoint (elems t) (elems u) =>
  ! d \in elems u.
proof.
move => c_d_in_pcs_t disj_t_u.
case (d \in elems u) => [d_in_elems_u | //].
have d_in_elems_t : d \in elems t by smt(poten_cmps_subset productP).
by rewrite /= -(in_fset0 d) -disj_t_u in_fsetI.
qed.

(* the potential comparison requests never increase, as we step *)

lemma is_worked_poten_cmps_step (t : term) :
  proper t => is_worked (step t) =>
  poten_cmps (of_worked (step t)) \subset poten_cmps t.
proof.
elim t => //.
move => xs prop_t /=.
case (size xs <= 1) => [le1_size_xs _ | gt1_size_xs _].
rewrite sub0set.
rewrite lerNgt /= in gt1_size_xs.
have xs_eq := cat_take_drop (size xs %/ 2) xs.
rewrite subsetP => [[a b]].
rewrite !in_fsetU !productP =>
  [[[[a_in_take_xs b_in_take_xs] | [a_in_drop_xs b_in_drop_xs]] |
   [a_in_take_xs b_in_drop_xs]]].
rewrite -xs_eq oflist_cat !in_fsetU /#.
rewrite -xs_eq oflist_cat !in_fsetU /#.
rewrite -xs_eq oflist_cat !in_fsetU /#.
move => i t IHt /= [#] _ prop_t _.
case (is_worked (step t)) => [is_wkd_step_t _ | not_is_wkd_step_t].
by rewrite IHt.
case (is_compare (step t)) => [/# | not_is_cmp_step_t _].
rewrite sub0set.
move => t u IHt IHu /= [#] prop_t prop_u _ _ _.
case (is_worked (step t)) => [is_wkd_step_t _ | not_is_wkd_step_t].
rewrite subsetP => [[a b]].
rewrite !in_fsetU !productP =>
  [[[/# | /#] | [a_in_elems_of_wkd_step_t -> /=]]].
right; by rewrite -is_worked_proper_step_elems_eq.
case (is_compare (step t)) => [/# | not_is_cmp_step_t].
case (is_worked (step u)) => [is_wkd_step_u | not_is_wkd_step_u].
rewrite subsetP => [[a b]].
rewrite !in_fsetU !productP =>
  [[[/# | /#] | [-> b_in_elems_of_wkd_step_u /=]]].
right; by rewrite -is_worked_proper_step_elems_eq.
case (is_compare (step u)) => [/# | not_is_cmp_step_u].
case (of_list t = []) => [of_list_t_eq_nil _ | of_list_t_ne_nil].
rewrite subsetP => p.
by rewrite !in_fsetU => ->.
case (of_list u = []) => [of_list_u_eq_nil _ | of_list_u_ne_nil _].
rewrite subsetP => p.
by rewrite !in_fsetU => ->.
have is_list_t : is_list t by rewrite -step_done_iff eq_done_iff.
have is_list_u : is_list u by rewrite -step_done_iff eq_done_iff.
have of_list_t_eq := head_behead (of_list t) 0 _ => //.
have of_list_u_eq := head_behead (of_list u) 0 _ => //.
rewrite subsetP => [[a b]].
rewrite !in_fsetU !productP !oflist_cons !in_fsetU !in_fset1 =>
  [[[-> [-> | ] |]]].
right.
rewrite {1}is_list //= mem_oflist -{1}of_list_t_eq /=.
by rewrite {1}(is_list u) //= mem_oflist -{1}of_list_u_eq.
rewrite mem_oflist => /mem_behead b_in_of_list_u.
right.
rewrite {1}is_list //= mem_oflist -{1}of_list_t_eq /=.
rewrite {1}(is_list u) //= mem_oflist //.
rewrite mem_oflist => /mem_behead a_in_of_list_t [-> |].
right.
rewrite {1}is_list //= mem_oflist a_in_of_list_t /=.
by rewrite {1}(is_list u) //= mem_oflist // -{1}of_list_u_eq.
rewrite mem_oflist => /mem_behead b_in_of_list_t.
right.
rewrite {1}is_list //= mem_oflist a_in_of_list_t.
by rewrite {1}is_list //= mem_oflist.
qed.

lemma is_compare_poten_cmps_step (t : term) :
  proper t => is_compare (step t) =>
  of_compare (step t) \in poten_cmps t.
proof.
elim t => //.
move => xs /=.
by case (size xs <= 1).
move => i t IHt /= [#] _ prop_t _.
case (is_worked (step t)) => [// | not_is_wkd_step_t].
case (is_compare (step t)) => [is_cmp_step_t _ /# | //].
move => t u IHt IHu /= [#] prop_t prop_u _ _ _.
case (is_worked (step t)) => [// | not_is_wkd_step_t].
case (is_compare (step t)) => [is_cmp_step_t _ | is_not_cmp_step_t].
rewrite !in_fsetU.
left; left; smt().
case (is_worked (step u)) => [// | not_is_wkd_step_u].
case (is_compare (step u)) => [is_cmp_step_u _ | is_not_cmp_step_u].
rewrite !in_fsetU.
left; right; smt().
case (of_list t = []) => [// | _].
by case (of_list u = []).
move => i j us vs /=.
by rewrite /proper_list0 /= !oflist_cons !productP !in_fsetU !in_fset1.
qed.

(* potential comparison requests invariant, where qs are sets of
   queries (encodings of comparison requests) *)

op poten_cmps_invar (t : term, qs : int fset) : bool =
  disjoint (poten_cmps t) (image dec qs).

lemma poten_cmps_invar_start :
  poten_cmps_invar (Sort range_len) fset0.
proof.
by rewrite /poten_cmps_invar image0 fsetI0.
qed.

lemma poten_cms_invar_is_worked (t : term, qs : int fset) :
  proper t => is_worked (step t) =>
  poten_cmps_invar t qs =>
  poten_cmps_invar (of_worked (step t)) qs.
proof.
rewrite /poten_cmps_invar => prop_t is_wkd_step_t disj_t_u.
rewrite disjointP => x x_in_pcs_of_wkd_step_t.
have x_in_pcs_t : x \in poten_cmps t by rewrite is_worked_poten_cmps_step.
case (x \in image dec qs) => [x_in_image_dec_qs | //].
by rewrite /= -(in_fset0 x) -disj_t_u in_fsetI.
qed.

lemma is_compare_poten_cmps_invar_not_query (t : term, qs : int fset) :
  proper t => is_compare (step t) =>
  poten_cmps_invar t qs =>
  ! enc (of_compare (step t)) \in qs.
proof.
rewrite /poten_cmps_invar => prop_t is_cmp_step_t disj_t_u.
have [rang1 rang2] := is_compare_proper_step_range t _ _ => //.
case (enc (of_compare (step t)) \in qs) => [enc_of_cmp_step_t_in_qs | //].
have of_cmp_step_t_in_image_dec_qs /= : of_compare (step t) \in image dec qs.
  have -> : of_compare (step t) = dec (enc (of_compare (step t))).
    rewrite encK // /#.
by rewrite mem_image.
rewrite -(in_fset0 (of_compare (step t))) -disj_t_u in_fsetI.
rewrite of_cmp_step_t_in_image_dec_qs /=.
by rewrite is_compare_poten_cmps_step.
qed.

lemma poten_cmps_answer (t : term, b : bool) :
  proper t => is_compare (step t) =>
  poten_cmps (oget (answer t b)) \subset
  poten_cmps t `\` fset1 (of_compare (step t)).
proof.
elim t => //.
move => xs /=; by case (size xs <= 1).
move => i t IHt /= [#] _ prop_t _.
case (is_worked (step t)) => [// | not_is_wkd_step_t].
case (is_compare (step t)) => [is_cmp_step_t _ | //].
have -> : answer t b <> None.
rewrite -is_compare_step_iff_good_answer //=.
case b => [b_true | b_false] /=; rewrite subsetP => p /#.
move => t u IHt IHu /= [#] prop_t prop_u A disj_elems_t_u _.
case (is_worked (step t)) => [// | not_is_wkd_step_t].
case (is_compare (step t)) => [is_cmp_step_t _ | not_is_cmp_step_t].
have -> /= : ! is_list t by rewrite -step_done_iff eq_done_iff /#.
have -> /= : answer t b <> None.
  by rewrite -is_compare_step_iff_good_answer.
have pts_ans_t_b_subset_pts_t_min_of_cmp_step_t
     := IHt _ _ => //.
rewrite subsetP => [[c d]].
rewrite !in_fsetU in_fsetD1 !productP =>
  [[[c_d_in_pcs_ans_t_b | c_d_in_pcs_u] | [c_in_elems_ans_t_b d_in_elems_u]]].
split; first smt(in_fsetU in_fsetD1).
smt(in_fsetD1).
split; first smt(in_fsetU).
case ((c, d) = of_compare (step t)) => [c_d_eq_of_cmp_step_t | //].
have c_d_in_pcs_t : (c, d) \in poten_cmps t.
 by rewrite c_d_eq_of_cmp_step_t is_compare_poten_cmps_step.
smt(mem_poten_cmps_disjoint).
split.
rewrite in_fsetU productP.
right.
by rewrite -(proper_answer_elems_eq t b) // -is_compare_step_iff_good_answer.
case ((c, d) = of_compare (step t)) => [c_d_eq_of_cmp_step_t | //].
have c_d_in_pcs_t : (c, d) \in poten_cmps t.
 by rewrite c_d_eq_of_cmp_step_t is_compare_poten_cmps_step.
smt(mem_poten_cmps_disjoint_not_elems2).
case (is_worked (step u)) => [// | not_is_wkd_step_u].
case (is_compare (step u)) => [is_cmp_step_u _ | not_is_cmp_step_u].
have -> /= : is_list t by rewrite -step_done_iff eq_done_iff.
have -> /= : answer u b <> None.
  by rewrite -is_compare_step_iff_good_answer.
have pts_ans_u_b_subset_pts_u_min_of_cmp_step_u
     := IHu _ _ => //.
rewrite subsetP => [[c d]].
rewrite !in_fsetU in_fsetD1 !productP =>
  [[[c_d_in_pcs_t | c_d_in_pcs_ans_u_b] | [c_in_elems_t d_in_elems_ans_u_b]]].
split; first smt(in_fsetU).
case ((c, d) = of_compare (step u)) => [c_d_eq_of_cmp_step_u | //].
have c_d_in_pcs_u : (c, d) \in poten_cmps u.
 by rewrite c_d_eq_of_cmp_step_u is_compare_poten_cmps_step.
smt(mem_poten_cmps_disjoint).
split; first smt(in_fsetU in_fsetD1).
case ((c, d) = of_compare (step u)) => [c_d_eq_of_cmp_step_u | //].
smt(in_fsetU in_fsetD1).
split.
rewrite in_fsetU productP.
right.
by rewrite -(proper_answer_elems_eq u b) // -is_compare_step_iff_good_answer.
case ((c, d) = of_compare (step u)) => [c_d_eq_of_cmp_step_u | //].
have c_d_in_pcs_u : (c, d) \in poten_cmps u.
 by rewrite c_d_eq_of_cmp_step_u is_compare_poten_cmps_step.
have disj_u_t : disjoint (elems u) (elems t) by rewrite fsetIC.
smt(mem_poten_cmps_disjoint_not_elems1).
case (of_list t = []) => [// | not_of_list_t_eq_nil].
by case (of_list u = []).
move => i j us vs /= H.
rewrite !oflist_cons.
case b => [b_true | b_false] /=.
rewrite oflist_cons !fset0U subsetP => [[c d]].
rewrite in_fsetD1 !productP !in_fsetU !in_fset1 !mem_oflist /#.
rewrite oflist_cons !fset0U subsetP => [[c d]].
rewrite in_fsetD1 !productP !in_fsetU !in_fset1 !mem_oflist /#.
qed.

lemma poten_cmps_invar_is_compare_answer
      (t : term, qs : int fset, b : bool) :
  proper t => is_compare (step t) =>
  poten_cmps_invar t qs =>
  poten_cmps_invar
  (oget (answer t b))
  (qs `|` fset1 (enc (of_compare (step t)))).
proof.
rewrite /poten_cmps_invar =>
  prop_t is_cmp_step_t disj_pcs_t_image_dec_qs.
have pcs_ans_t_b_sub_pcs_t_min_of_cmp_step_t
     := poten_cmps_answer t b _ _ => //.
have [rang1 rang2] := is_compare_proper_step_range t _ _ => //.
rewrite disjointP => p p_in_pcs_ans_t_b.
rewrite imageP negb_exists => q /=.
rewrite in_fsetU1 negb_and negb_or.
have [p_in_pcs_t p_ne_cmp_step_t] :
  p \in poten_cmps t /\ p <> of_compare (step t).
  have := pcs_ans_t_b_sub_pcs_t_min_of_cmp_step_t p _ => //.
  by rewrite in_fsetD1.
case (dec q = p) => [dec_q_eq_p | //].
case (q \in qs) => [q_in_qs | not_q_in_qs /=].
right => /=.
rewrite -(in_fset0 p) -disj_pcs_t_image_dec_qs in_fsetI p_in_pcs_t /=.
by rewrite -dec_q_eq_p mem_image.
case (q = enc (of_compare (step t))) => [q_eq_enc_of_cmp_step_t | //].
move : dec_q_eq_p p_ne_cmp_step_t.
by rewrite q_eq_enc_of_cmp_step_t encK.
qed.

(* here is our algorithm: *)

module Alg : ALG = {
  var term : term

  proc init(aux : aux) : unit = {
    term <- Sort range_len;
  }

  proc make_query_or_report_output() : response = {
    var r : response;
    var stp : step;
    stp <- step term;
    while (stp <> Done /\ ! is_compare stp) {
      term <- of_worked stp;
      stp <- step term;
    }
    if (stp = Done) {  (* term = List ... *)
      r <- Response_Report (of_list term);
    }
    else {
      r <- Response_Query (enc (of_compare stp));
    }
    return r;
  }

  proc query_result(b : inp) : unit = {
    var oterm : term option;
    oterm <- answer term b;
    if (oterm = None) {  (* will not happen, but termination *)
      term <- List [0];  (* invariant only says term is proper *)
    }
    else {
      term <- oget oterm;
    }
  }
}.

(* algorithm's termination invariant, for use with G_ll *)

op alg_term_invar (x : glob Alg) : bool =
  proper x.

lemma Alg_init_term :
  phoare [Alg.init : true ==> alg_term_invar (glob Alg)] = 1%r.
proof.
proc; auto => &hr _.
rewrite /alg_term_invar proper_start.
qed.

lemma Alg_make_query_or_report_output_term :
  phoare
  [Alg.make_query_or_report_output :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r.
proof.
proc; wp; sp.
while
  (proper Alg.term /\ stp = step Alg.term)
  (metric Alg.term).
move => z.
auto =>
  &hr [#] prop_term stp_eq_step_term step_term_not_done
  not_is_cmp_step_term <- /=.
have is_wkd_step_term :
  is_worked (step Alg.term{hr}) by smt(is_worked_iff).
split.
smt(is_worked_proper_step).
by rewrite stp_eq_step_term metric_step.
auto; progress.
trivial.
have eq0_metric_term : metric term = 0 by smt(metric_ge0).
have := metric0_no_step term _ _ => //.
by rewrite is_worked_iff.
by rewrite /alg_term_invar.
qed.

lemma Alg_query_result_term :
  phoare
  [Alg.query_result :
   alg_term_invar (glob Alg) ==>
   alg_term_invar (glob Alg)] = 1%r.
proof.
proc; auto => &hr.
rewrite /alg_term_invar => prop_term.
rewrite /=.
case (answer Alg.term{hr} b{hr} = None) => [_ | ans_term_b_ne_none].
rewrite /proper_list0 /= in_range_len /= gt0_len.
smt(oget_some proper_answer).
qed.

(* here is the invariant for the proof of our main lemma *)

op nosmt invar (inpss : bool list list, qs : int fset, t : term) : bool =
  inpss_invar () inpss /\
  proper t /\
  all  (* this will hold vacuously if Adv makes inpss empty *)
  (fun inps =>
     repr (cmp_of_rel inps) t = sort (cmp_of_rel inps) range_len)
  inpss /\
  wc_term t + card qs <= wc len /\
  poten_cmps_invar t qs.

lemma invar_impl_inpss_invar (inpss : bool list list, qs : int fset, t : term) :
  invar inpss qs t => inpss_invar () inpss.
proof. by rewrite /invar. qed.

lemma invar_impl_all_inpss_total_ordering
      (inpss : bool list list, qs : int fset, t : term) :
  invar inpss qs t => all total_ordering inpss.
proof.
rewrite /invar => [[inpss_invar_inpss _]].
smt(inpss_invar_all_good_aux allP).
qed.

lemma invar_impl_all_repr_eq (inpss : bool list list, qs : int fset, t : term) :
  invar inpss qs t =>
  all
  (fun inps =>
     repr (cmp_of_rel inps) t = sort (cmp_of_rel inps) range_len)
  inpss.
proof. by rewrite /invar. qed.

lemma invar_impl_proper_term (inpss : bool list list, qs : int fset, t : term) :
  invar inpss qs t => proper t.
proof. by rewrite /invar. qed.

lemma invar_impl_wc_le (inpss : bool list list, qs : int fset, t : term) :
  invar inpss qs t => wc_term t + card qs <= wc len.
proof. by rewrite /invar. qed.

lemma invar_impl_poten_cmps_invar
      (inpss : bool list list, qs : int fset, t : term) :
  invar inpss qs t => poten_cmps_invar t qs.
proof. by rewrite /invar. qed.

lemma invar_start :
  invar (init_inpss ()) fset0 (Sort range_len).
proof.
rewrite /invar /=.
split; first rewrite inpss_invar_init.
split; first rewrite proper_list_range_len.
split; first by rewrite allP.
split; first by rewrite fcards0 /= size_range_len.
rewrite poten_cmps_invar_start.
qed.

lemma invar_is_worked_step
      (inpss : inp list list, qs : int fset, t : term) :
  invar inpss qs t => is_worked (step t) =>
  invar inpss qs (of_worked (step t)).
proof.
rewrite /invar =>
  [#] inpss_invar_inpss prop_t all_inpss_repr wc_term_ineq
  pci_t_qs is_wkd_step_t.
split; first trivial.
split; first by rewrite is_worked_proper_step.
split.
rewrite allP => inps inps_in_inpss /=.
rewrite is_worked_repr_step_cmp_of_rel //.
smt(inpss_invar_all_good_aux allP).
rewrite allP in all_inpss_repr.
by rewrite all_inpss_repr.
split; first smt(wc_term_step).
by rewrite poten_cms_invar_is_worked.
qed.

lemma invar_is_compare_answer
      (inpss : inp list list, qs : int fset, t : term, b : bool) :
  invar inpss qs t => is_compare (step t) =>
  invar
  (filter_nth inpss (enc (of_compare (step t))) b)
  (qs `|` fset1 (enc (of_compare (step t))))
  (oget (answer t b)).
proof.
rewrite /invar =>
  [#] inpss_invar_inpss prop_t all_inpss_repr wc_term_ineq
  pci_t_qs is_cmp_step_t.
split; first by rewrite inpss_invar_filter_nth.
split; first by rewrite proper_answer // -is_compare_step_iff_good_answer.
split.
rewrite allP => inps inps_in_filter_nth_inpss_enc_of_cmp_stp_t_b /=.
rewrite mem_filter /= in inps_in_filter_nth_inpss_enc_of_cmp_stp_t_b.
elim inps_in_filter_nth_inpss_enc_of_cmp_stp_t_b => [<- inps_in_inpss].
have -> :
  nth witness inps (enc (of_compare (step t))) =
  cmp_of_rel inps (of_compare (step t)).`1 (of_compare (step t)).`2.
  rewrite cmp_of_rel_pair_eq //.
  smt(inpss_invar_all_good_aux allP).
  by rewrite is_compare_proper_step_range1.
  by rewrite is_compare_proper_step_range2.
rewrite allP in all_inpss_repr.
by rewrite is_compare_step_answer_repr // all_inpss_repr.
split.
rewrite fcardUindep1 1:is_compare_poten_cmps_invar_not_query // !addrA -ltzE.
rewrite (ltr_le_trans (wc_term t + card qs)) //.
by rewrite ltr_add2r wc_term_answer 1:/# -is_compare_step_iff_good_answer.
by rewrite poten_cmps_invar_is_compare_answer.
qed.

lemma invar_inpss_is_list_answer
      (inpss : inp list list, qs : int fset, t : term) :
  invar inpss qs t => inpss <> [] => is_list t =>
  inpss_answer () inpss (of_list t).
proof.
move => invar_inpss_qs_t inpss_ne_nil is_list_t.
rewrite /inpss_answer.
split; first trivial.
move => out_opt.
rewrite mapP => [[inps [inps_in_inpss ->]]].
rewrite /f.
have -> /= : total_ordering inps.
  smt(invar_impl_all_inpss_total_ordering allP).
rewrite /total_ordering_to_perm_len /tsort.
rewrite -(repr_done (cmp_of_rel inps)) //.
smt(invar_impl_all_repr_eq allP).
qed.

(* here is our main lemma, parameterized by an upper bound: *)

lemma G_main (bound : int) (Adv <: ADV{-Alg}) :
  wc len <= bound =>
  hoare
  [G(Alg, Adv).main :
   true ==> ! res.`1 /\ res.`2 <= bound].
proof.
move => wc_len_le_bound.
proc.
seq 7 :
  (inpss = init_inpss () /\ !error /\ don = (inpss = []) /\
   stage = 0 /\ queries = fset0 /\ Alg.term = Sort range_len).
inline Alg.init; wp.
call (_ : true); first auto.
while
  (stage = card queries /\ !error /\ (!don => inpss <> []) /\
   invar inpss queries Alg.term).
inline Alg.make_query_or_report_output.
seq 2 :
  (stage = card queries /\ !error /\ inpss <> [] /\
   invar inpss queries Alg.term /\
   stp = step Alg.term /\ (stp = Done \/ is_compare stp)).
while (stp = step Alg.term /\ invar inpss queries Alg.term).
auto; progress [-delta].
by rewrite invar_is_worked_step // is_worked_iff.
auto; smt().
if.
sp.
rcondf 1; first auto; smt().
sp 1.
rcondt 1; first auto; progress [-delta].
rewrite (invar_inpss_is_list_answer inpss{hr} queries{hr}) //.
by rewrite -step_done_iff.
auto.
sp 2.
rcondt 1; first auto.
sp.
rcondt 1; first auto => |> &hr _ _ inv [// | is_cmp_step_term _].
have prop_term : proper Alg.term{hr}.
  by rewrite (invar_impl_proper_term inpss{hr} queries{hr}).
rewrite enc_bounds_ge0 1:is_compare_proper_step_range1 //
        1:is_compare_proper_step_range2 //=.
rewrite enc_bounds_lt_arity 1:is_compare_proper_step_range1 //
        1:is_compare_proper_step_range2 //=.
by rewrite is_compare_poten_cmps_invar_not_query //
           (invar_impl_poten_cmps_invar inpss{hr} queries{hr}).
sp 2; elim* => stage' queries'.
seq 1 :
  (queries = queries' `|` fset1 i /\
   stage = stage' + 1 /\
   i = oget (dec_response_query resp) /\
   resp = Response_Query (enc (of_compare stp)) /\
   stage' = card queries' /\ !error /\ inpss <> [] /\
   invar inpss queries' Alg.term /\
   stp = step Alg.term /\ is_compare stp).
call (_ : true); first auto; progress [-delta]; smt().
inline Alg.query_result.
sp 2.
rcondf 1; first auto => |> &hr _ inpss_ne_nil inv is_cmp_step_term.
have prop_term : proper Alg.term{hr}.
  by rewrite (invar_impl_proper_term inpss{hr} queries').
by rewrite -is_compare_step_iff_good_answer.
auto => |> &hr _ inps_ne_nil inv is_cmp_step_term.
have prop_term : proper Alg.term{hr}.
  by rewrite (invar_impl_proper_term inpss{hr} queries').
split => _;
  (split;
   [by rewrite fcardUindep1 // 1:is_compare_poten_cmps_invar_not_query //
               1:(invar_impl_poten_cmps_invar inpss{hr}) |
    by rewrite invar_is_compare_answer]).
auto; progress [-delta].
by rewrite fcards0.
rewrite invar_start.
rewrite (ler_trans (wc len)) //.
smt(invar_impl_wc_le wc_term_ge0 invar_impl_proper_term).
qed.

(* here is the generalized version of our main theorem: *)

lemma upper_bound_gen (bound : int) &m :
  wc len <= bound =>
  phoare
  [Alg.init : true ==> alg_term_invar (glob Alg)] = 1%r /\
  phoare
  [Alg.make_query_or_report_output :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r /\
  phoare
  [Alg.query_result :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r /\
  (forall (Adv <: ADV{-Alg}) (adv_term_invar : glob Adv -> bool),
   phoare
   [Adv.init : true ==> adv_term_invar (glob Adv)] = 1%r =>
   phoare
   [Adv.ans_query :
    adv_term_invar (glob Adv) ==> adv_term_invar (glob Adv)] = 1%r =>
   Pr[G(Alg, Adv).main() @ &m :
        ! res.`1 /\ res.`2 <= bound] = 1%r).
proof.
move => wc_len_le_bound.
split; first apply Alg_init_term.
split; first apply Alg_make_query_or_report_output_term.
split; first apply Alg_query_result_term.
move => Adv adv_term_invar Adv_init_term Adv_ans_query_term.
byphoare
  (_ : true ==> ! res.`1 /\ res.`2 <= bound) => //.
conseq
  (_ : true ==> true)
  (_ : true ==> ! res.`1 /\ res.`2 <= bound) => //.
by conseq (G_main bound Adv _).
rewrite (G_ll Alg Adv alg_term_invar adv_term_invar) 1:Alg_init_term
        1:Alg_make_query_or_report_output_term 1:Alg_query_result_term
        1:Adv_init_term Adv_ans_query_term.
qed.

(* and below are two instantiations of our general theorem,
   first for the bound wc len, and second for the bound
   len * int_log 2 len *)

lemma upper_bound_wc &m :
  phoare
  [Alg.init : true ==> alg_term_invar (glob Alg)] = 1%r /\
  phoare
  [Alg.make_query_or_report_output :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r /\
  phoare
  [Alg.query_result :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r /\
  (forall (Adv <: ADV{-Alg}) (adv_term_invar : glob Adv -> bool),
   phoare
   [Adv.init : true ==> adv_term_invar (glob Adv)] = 1%r =>
   phoare
   [Adv.ans_query :
    adv_term_invar (glob Adv) ==> adv_term_invar (glob Adv)] = 1%r =>
   Pr[G(Alg, Adv).main() @ &m :
        ! res.`1 /\ res.`2 <= wc len] = 1%r).
proof.
by apply (upper_bound_gen (wc len) &m).
qed.

lemma upper_bound_len_int_log2_len &m :
  phoare
  [Alg.init : true ==> alg_term_invar (glob Alg)] = 1%r /\
  phoare
  [Alg.make_query_or_report_output :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r /\
  phoare
  [Alg.query_result :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r /\
  (forall (Adv <: ADV{-Alg}) (adv_term_invar : glob Adv -> bool),
   phoare
   [Adv.init : true ==> adv_term_invar (glob Adv)] = 1%r =>
   phoare
   [Adv.ans_query :
    adv_term_invar (glob Adv) ==> adv_term_invar (glob Adv)] = 1%r =>
   Pr[G(Alg, Adv).main() @ &m :
        ! res.`1 /\ res.`2 <= len * int_log 2 len] = 1%r).
proof.
apply (upper_bound_gen (len * int_log 2 len) &m).
rewrite wc_le ge1_len.
qed.
