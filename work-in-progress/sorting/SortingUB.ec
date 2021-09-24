(* Application of Upper Bounds Framework to Comparison-based
   Sorting *)

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

require import AllCore List IntDiv StdOrder IntMin FSetAux Perms Binomial WF.
import IntOrder.

require UpperBounds.       (* adversarial lower bounds framework *)
require import ListSizes.  (* showing uniq lists have the same size *)
require import AllLists.   (* generating all lists of length over universe *)
require import IntLog.     (* integer logarithms *)

require import SortingProb.  (* comparison-based sorting problem *)

clone import UpperBounds as UB with
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

(* wc : int -> int recursively calculates an upper bound on the worst
   case number of comparisons used by merge sort when given a list of
   size n *)

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
  lt_nat           (* well-founded relation being used *)
  0                (* element to be returned if recursive calls
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
have -> /= : lt_nat (n %/ 2) n by smt().
have -> /= : lt_nat (n %%/ 2) n by smt().
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
have -> // : lt_nat (n %%/ 2) n by smt().
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
have -> /= : lt_nat (n %/ 2) n by smt().
have -> /= : lt_nat (n %%/ 2) n by smt().
rewrite -/wc.
rewrite (IH (n %/ 2)) 1:/# 1:/#.
rewrite (IH (n %%/ 2)) 1:/# 1:/#.
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

lemma wc_le (n : int) :
  1 <= n => wc n <= n * int_log 2 n.
proof.
move => ge1_n.
rewrite wc_eq // ler_subl_addr ler_addl.
smt(int_log_ub_lt).
qed.

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

lemma cat_eq_nil_iff (xs ys : 'a list) :
  xs ++ ys = [] <=> xs = [] /\ ys = [].
proof. by case xs. qed.

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
  with t = List _       => []
  with t = Cons _ _     => []
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

op proper_list0 (xs : int list) : bool =
  uniq xs /\ all (mem range_len) xs.

op proper_list (xs : int list) : bool =
  xs <> [] /\ uniq xs /\ all (mem range_len) xs.

lemma proper_list_from0 (xs : int list) :
  proper_list xs => proper_list0 xs.
proof.
by rewrite /proper_list /proper_list0.
qed.

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

op elems (t : term) : int fset =
  with t = Sort xs        => oflist xs
  with t = List xs        => oflist xs
  with t = Cons i u       => fset1 i `|` elems u
  with t = Merge u v      => elems u `|` elems v
  with t = Cond i j us vs => fset1 i  `|` fset1 j  `|` oflist us `|` oflist vs.

lemma is_list_elems (t : term) :
  is_list t => oflist (of_list t) = elems t.
proof. by case t. qed.

op proper (t : term) : bool =
  with t = Sort xs        => proper_list xs
  with t = List xs        => proper_list0 xs
  with t = Cons i u       =>
    mem range_len i /\ proper u /\ ! mem (elems u) i
  with t = Merge u v      =>
    proper u /\ proper v /\ (is_list v => is_list u) /\
    elems u `&` elems v = fset0 /\ elems u `|` elems v <> fset0
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

type step = [  (* result of call to step on term t *)
  | Done                  (* t is fully evaluated - List ... *)
  | Compare of int & int  (* t's evaluation needs answer to query *)
  | Worked  of term       (* the step succeeded *)
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

lemma proper_step_gen (t : term) :
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
  [is_cmp_step_t is_wrkd_step_t | not_is_cmp_step_t _].
smt(eq_done_iff).
have is_list_t : is_list t by rewrite -step_done_iff eq_done_iff.
split; first by rewrite oflist_cons is_list_elems.
split; first by rewrite fset1_union_any_ne_fset0.
rewrite proper_list0_cons //.
by rewrite -is_list_proper_iff.
by rewrite is_list_mem_iff.
move => t u IHt IHu.
rewrite /= =>
  [#] prop_t prop_u is_list_imp_u_t disj_t_u
  elems_t_union_elems_u_ne_fset0.
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

lemma proper_step (t : term) :
  proper t => is_worked (step t) => proper (of_worked (step t)).
proof. smt(proper_step_gen). qed.

lemma is_worked_step_elems_eq (t : term) :
  proper t => is_worked (step t) =>
  elems (of_worked (step t)) = elems t.
proof. smt(proper_step_gen). qed.

lemma is_worked_step_elems_ne (t : term) :
  proper t => is_worked (step t) => elems (of_worked (step t)) <> fset0.
proof. smt(proper_step_gen). qed.

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

lemma size_term_ge1_when_proper_elems_ne (t : term) :
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
rewrite size_term_eq_card_elems 1:proper_step //.
by rewrite size_term_eq_card_elems // is_worked_step_elems_eq.
qed.

lemma repr_start (cmp : int -> int -> bool) :
  repr cmp (Sort range_len) = sort cmp range_len.
proof. trivial. qed.

lemma repr_step (cmp : int -> int -> bool, t : term) :
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

(* supporting lemma for termination metric for step *)

lemma square_divide_lt (n : int) :
  2 <= n =>
  1 + (n %/ 2) ^ 2 + (n %%/ 2) ^ 2 < n ^ 2.
proof.
move => ge2_n.
have -> : n ^ 2 = (n %/ 2 + n %%/ 2) ^ 2 by rewrite {1}div2_plus_div2up_eq.
rewrite 3!expr2.
have -> /# :
  (n %/ 2 + n %%/ 2) * (n %/ 2 + n %%/ 2) =
  (n %/ 2) * (n %/ 2) + (n %/ 2) * (n %%/ 2) +
  (n %%/ 2) * (n %/ 2) + (n %%/ 2) * (n %%/ 2).
  algebra.
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

lemma proper_answer_gen (t : term, b : bool) :
  proper t => answer t b <> None =>
  proper (oget (answer t b)) /\ elems (oget (answer t b)) = elems t /\
  elems t <> fset0 /\ (is_list (oget (answer t b)) = is_list t).
proof.
elim t => //.
move => i u IH /= [#] i_in_range prop_u i_not_in_elems_u.
case (answer u b = None) => [// | ans_u_b_ne_none _].
rewrite oget_some /= i_in_range /=.
split; first smt().
split; first smt().
by rewrite fset1_union_any_ne_fset0.
move => t u IHt IHu /= [#] prop_t prop_u is_list_imp_u_t disj_t_u.
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

lemma proper_answer_elems_ne (t : term, b : bool) :
  proper t => answer t b <> None => elems (oget (answer t b)) <> fset0.
proof. smt(proper_answer_gen). qed.

lemma is_compare_step_impl_good_answer(t : term, b : bool) :
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

lemma is_compare_step_repl (cmp : int -> int -> bool, t : term) :
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
  smt(is_compare_step_impl_good_answer).
by rewrite IH.
move => t u IHt IHu /= [#] prop_t prop_u _ _.
case (is_worked (step t)) => [// | not_is_wkd_step_t].
case (is_compare (step t)) => [is_cmp_step_t _ | not_is_cmp_step_t].
have -> /= :
  answer t (cmp (of_compare (step t)).`1 (of_compare (step t)).`2) <> None.
  smt(is_compare_step_impl_good_answer).
have -> /= : ! is_list t.
  rewrite -step_done_iff eq_done_iff negb_and /=.
  by left.
by rewrite IHt.
case (is_worked (step u)) => [// | not_is_wkd_step_u].
case (is_compare (step u)) => [is_cmp_step_u _ | not_is_cmp_step_u].
have -> /= :
  answer u (cmp (of_compare (step u)).`1 (of_compare (step u)).`2) <> None.
  smt(is_compare_step_impl_good_answer).
have -> /= :
  answer t (cmp (of_compare (step u)).`1 (of_compare (step u)).`2) = None.
  smt(is_compare_step_impl_good_answer).
have -> /= : is_list t by rewrite -step_done_iff eq_done_iff.
by rewrite IHu.
case (of_list t = []) => [// | _].
by case (of_list u = []).
move => i j us vs /= _.
by case (cmp i j) => [cmp_i_j | not_cmp_i_j].
qed.

(* an upper bound on the number of comparisions/answers it will
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
smt(size_term_ge1_when_proper_elems_ne size_term_ge0).
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
smt(is_list_elems size_term_ge1_when_proper_elems_ne).
case (of_list u = []) => [of_list_u_eqnil _ | of_list_u_nenil _].
move : elems_t_union_elems_u_ne_fset0.
rewrite -is_list_elems // -is_list_elems //.
rewrite of_list_u_eqnil -set0E fsetU0 => oflist_of_list_u_ne_fset0.
rewrite (is_list u) // of_list_u_eqnil /=.
smt(is_list_elems size_term_ge1_when_proper_elems_ne).
rewrite (is_list t) // (is_list u) //=.
have <- := head_behead (of_list t) 0 _ => //.
have <- := head_behead (of_list u) 0 _ => //#.
qed.

(* when we answer a comparision query, wc_term always gets strictly
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
      term <- oget (answer term b);
    }
  }
}.

(* algorithm's termination invariant *)

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
smt(proper_step).
rewrite stp_eq_step_term.
rewrite metric_step.
trivial.
trivial.
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
case (answer Alg.term{hr} b{hr} = None) => [_ | ans_term_b_ne_none].
rewrite /proper_list0 /= in_range_len /= gt0_len.
smt(proper_answer).
qed.

(* the main lemma: *)

lemma G_main (aux' : aux, inps' : inp list) :
  hoare
  [G(Alg).main :
   aux = aux' /\ inps = inps' /\ size inps = arity /\
   all (mem univ) inps /\ good aux inps ==>
   res.`1 = f aux' inps' /\ res.`2 <= len * int_log 2 len].
proof.
admit.
qed.

(* here is our main theorem: *)

lemma upper_bound &m :
  phoare
  [Alg.init : true ==> alg_term_invar (glob Alg)] = 1%r /\
  phoare
  [Alg.make_query_or_report_output :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r /\
  phoare
  [Alg.query_result :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r /\
  (forall (aux : aux, inps : inp list),
   size inps = arity => all (mem univ) inps => good aux inps =>
   Pr[G(Alg).main(aux, inps) @ &m :
      res.`1 = f aux inps /\ res.`2 <= len * int_log 2 len] = 1%r).
proof.
split; first apply Alg_init_term.
split; first apply Alg_make_query_or_report_output_term.
split; first apply Alg_query_result_term.
move => aux' inps' size_inps'_eq_arity all_inps'_in_univ good_aux'_inps'.
byphoare
  (_ :
   aux = aux' /\ inps = inps' /\ size inps = arity /\
   all (mem univ) inps /\ good aux inps ==>
   res.`1 = f aux' inps' /\ res.`2 <= len * int_log 2 len) => //.
conseq
  (_ : true ==> true)
  (_ :
   aux = aux' /\ inps = inps' /\ size inps = arity /\
   all (mem univ) inps /\ good aux inps ==>
   res.`1 = f aux' inps' /\ res.`2 <= len * int_log 2 len) => //.
by conseq (G_main aux' inps').
rewrite (G_ll Alg alg_term_invar) 1:Alg_init_term
        1:Alg_make_query_or_report_output_term Alg_query_result_term.
qed.
