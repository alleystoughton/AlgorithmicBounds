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

op merge (cmp : 'a -> 'a -> bool, xs ys : 'a list) : 'a list =
  with xs = [],      ys = []      => []
  with xs = [],      ys = _ :: _  => ys
  with xs = _ :: _,  ys = []      => xs
  with xs = u :: us, ys = v :: vs =>
    if cmp u v
    then u :: merge cmp us ys
    else v :: merge cmp xs vs.

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
  with t = Sort _         => true
  with t = List _         => false
  with t = Cons _ _       => false
  with t = Merge _ _      => false
  with t = Cond i j us vs => false.

op of_sort (t : term) : int list =
  with t = Sort xs        => xs
  with t = List xs        => []
  with t = Cons i u       => []
  with t = Merge u v      => []
  with t = Cond i j us vs => [].

lemma is_sort (t : term) :
  is_sort t => t = Sort (of_sort t).
proof. by case t. qed.

op is_list (t : term) : bool =
  with t = Sort xs        => false
  with t = List xs        => true
  with t = Cons i u       => false
  with t = Merge u v      => false
  with t = Cond i j us vs => false.

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

op proper_list (xs : int list) : bool =
  xs <> [] /\ uniq xs /\ all (mem range_len) xs.

lemma proper_list_split (xs ys : int list) :
  proper_list (xs ++ ys) => xs <> [] => ys <> [] =>
  proper_list xs /\ proper_list ys /\ ! has (mem ys) xs.
proof.
by rewrite /proper_list has_sym all_cat cat_uniq.
qed.

lemma proper_list_cons (i : int, xs : int list) :
  proper_list xs => mem range_len i => ! mem xs i =>
  proper_list (i :: xs).
proof. by rewrite /proper_list. qed.

lemma proper_list_cat (xs ys : int list) :
  proper_list xs => proper_list ys => ! has (mem xs) ys =>
  proper_list (xs ++ ys).
proof.
rewrite /proper_list =>
  [#] nonnil_xs uniq_xs all_in_range_xs
  [#] nonnil_ys uniq_ys all_in_range_ys
  disj_xs_ys.
split; first smt(cat_eq_nil_iff).
split; first by rewrite cat_uniq.
by rewrite all_cat.
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
  with t = List xs        => proper_list xs
  with t = Cons i u       =>
    mem range_len i /\ proper u /\ ! mem (elems u) i
  with t = Merge u v      =>
    proper u /\ proper v /\ (is_list v => is_list u) /\
    elems u `&` elems v = fset0
  with t = Cond i j us vs =>
    mem range_len i /\ mem range_len j /\
    all (mem range_len) us /\ all (mem range_len) vs /\
    ! mem us i /\ ! mem vs j /\
    ! mem vs i /\ ! mem us j /\
    ! has (mem us) vs.

lemma is_list_proper_iff (t : term) :
  is_list t => proper t <=> proper_list (of_list t).
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

lemma step_compare_iff (t : term, i j : int) :
  step t = Compare i j <=>
  (exists (n : int, u : term),
   t = Cons n u /\ step u = Compare i j) \/
  (exists (u v : term),
   t = Merge u v /\ step u = Compare i j) \/
  (exists (xs : int list, v : term),
   t = Merge (List xs) v /\ step v = Compare i j) \/
  (exists (us vs : int list), t = Cond i j us vs).
proof.
case t.
smt().
smt().
move => n u.
split => [H | /#].
left; exists n u; smt().
move => u v.
split => [/= | /#].
case (is_worked (step u)) => [// | not_is_worked_u].
case (is_compare (step u)) =>
  [is_compare_u step_u_eq_Compare_i_j | not_is_compare_u].
left; by exists u v.
case (is_worked (step v)) => [// | not_is_worked_v].
case (is_compare (step v)) =>
  [is_compare_v step_u_eq_Compare_i_j | not_is_compare_v].
right.
have is_list_u : is_list u.
  move : not_is_worked_u not_is_compare_u.
  case u; smt().
have [xs ->] : exists xs, u = List xs.
  move : is_list_u.  
  clear not_is_worked_u not_is_compare_u.
  (case u; first smt()); last 3 smt().
  move => ys _; by exists ys.
by exists xs v.
smt().
smt().
qed.

lemma proper_step (t : term) :
  proper t => is_worked (step t) =>
  elems (of_worked (step t)) = elems t /\ proper (of_worked (step t)).
proof.
elim t.
move => xs /=.
case (size xs <= 1) => [// | gt1_size_xs pl_xs _].
rewrite lerNgt /= in gt1_size_xs.
have xs_eq := cat_take_drop (size xs %/ 2) xs.
split; first by rewrite -{5}xs_eq oflist_cat.
have pls_xs :=
     proper_list_split (take (size xs %/ 2) xs) (drop (size xs %/ 2) xs)
     _ _ _ => //.
  smt().
  rewrite -size_eq0 size_take /#.
  rewrite -size_eq0 size_drop /#.
split; first by elim pls_xs.
split => [| /=]; first by elim pls_xs.
rewrite disjointP => x.
rewrite 2!mem_oflist.
smt(hasPn).
trivial.
move => i t IH /= [i_in_range [prop_t not_i_in_elems_t]].
case (is_worked (step t)) => [is_wkd_step_t | not_is_wkd_step_t].
have [elems_eq prop_of_wrkd_step_t] := IH _ _ => //.
by rewrite elems_eq /= prop_of_wrkd_step_t.
case (is_compare (step t)) =>
  [is_cmp_step_t is_wrkd_step_t | not_is_cmp_step_t _].
smt(eq_done_iff).
have is_list_t : is_list t by rewrite -step_done_iff eq_done_iff.
split; first by rewrite oflist_cons is_list_elems.
rewrite proper_list_cons //.
by rewrite -is_list_proper_iff.
by rewrite is_list_mem_iff.
move => t u IHt IHu.
rewrite /= => [#] prop_t prop_u is_list_imp_u_t disj_t_u.
case (is_worked (step t)) => [is_wkd_step_t _ | not_is_wkd_step_t].
have [elems_eq prop_of_wrkd_step_t] := IHt _ _ => //.
rewrite elems_eq /= prop_of_wrkd_step_t prop_u /=.
split => [is_list_u | //].
smt(step_done_iff).
case (is_compare (step t)) => [is_cmp_step_t | not_is_cmp_step_t].
smt(step_compare_iff).
case (is_worked (step u)) => [is_wkd_step_u _ | not_is_wkd_step_u].
have [elems_eq prop_of_wrkd_step_u] := IHu _ _ => //.
rewrite elems_eq /= prop_of_wrkd_step_u prop_t /=.
split => [is_list_of_wkd_step_u | //].
by rewrite -step_done_iff eq_done_iff.
case (is_compare (step u)) => [is_cmp_step_u | not_is_cmp_step_u].
smt(step_compare_iff).
case (of_list t = []) => [| of_list_t_ne_nil].
rewrite -(is_list_elems t) 1:-step_done_iff 1:eq_done_iff //.
move => -> /=; by rewrite -set0E fset0U.
case (of_list u = []) => [| of_list_u_ne_nil].
rewrite -(is_list_elems u) 1:-step_done_iff 1:eq_done_iff //.
move => -> /=; by rewrite -set0E fsetU0.
move => _.
have is_list_t : is_list t by rewrite -step_done_iff eq_done_iff.
have is_list_u : is_list u by rewrite -step_done_iff eq_done_iff.
split.
rewrite -(is_list_elems t) // -(is_list_elems u) //.
rewrite -{3}(head_behead (of_list t) 0) //.
rewrite -{3}(head_behead (of_list u) 0) //.
rewrite 2!oflist_cons.
smt(fsetUC fsetUA).
have proper_list_of_list_t :
  proper_list (of_list t) by rewrite -is_list_proper_iff.
have proper_list_of_list_u :
  proper_list (of_list u) by rewrite -is_list_proper_iff.
split; first smt(allP mem_head_behead).
split; first smt(allP mem_head_behead).
have of_list_t_eq := head_behead (of_list t) 0 _ => //.
have of_list_u_eq := head_behead (of_list u) 0 _ => //.
split; first smt(allP).
split; first smt(allP).
split; first smt().
split; first smt().
have all_in_of_list_t_not_in_of_list_u :
  forall (x : int), x \in of_list t => ! (x \in of_list u).
  move => x x_in_of_list_t.
  move : disj_t_u.
  rewrite disjointP -is_list_elems // -is_list_elems // => H.
  by rewrite -mem_oflist // H 1:mem_oflist.
have all_in_of_list_u_not_in_of_list_t :
  forall (x : int), x \in of_list u => ! (x \in of_list t).
  smt(hasPn).
split.
have hd_of_list_t_in_of_list_t : head 0 (of_list t) \in of_list t.
  by rewrite -{1}of_list_t_eq in_cons.
case (head 0 (of_list t) \in behead (of_list u)) =>
  [hd_of_list_t_in_behead_of_list_u | //].
have hd_of_list_t_in_of_list_u : head 0 (of_list t) \in of_list u.
  by rewrite -{1}of_list_u_eq in_cons hd_of_list_t_in_behead_of_list_u.
have // : ! (head 0 (of_list t) \in of_list u).
  by rewrite all_in_of_list_t_not_in_of_list_u 1:hd_of_list_t_in_of_list_t.
split.
have hd_of_list_u_in_of_list_u : head 0 (of_list u) \in of_list u.
  by rewrite -{1}of_list_u_eq in_cons.
case (head 0 (of_list u) \in behead (of_list t)) =>
  [hd_of_list_u_in_behead_of_list_t | //].
have hd_of_list_t_in_of_list_u : head 0 (of_list u) \in of_list t.
  by rewrite -{1}of_list_t_eq in_cons hd_of_list_u_in_behead_of_list_t.
have // : ! (head 0 (of_list u) \in of_list t).
  by rewrite all_in_of_list_u_not_in_of_list_t 1:hd_of_list_u_in_of_list_u.
rewrite hasPn => x x_in_behead_of_list_u.
case (x \in behead (of_list t)) => [x_in_behead_of_list_t | //].
have x_in_of_list_t : x \in of_list t.
  by rewrite -of_list_t_eq in_cons x_in_behead_of_list_t.
have x_in_of_list_u : x \in of_list u.
  by rewrite -of_list_u_eq in_cons x_in_behead_of_list_u.
have // : ! (x \in of_list t) by rewrite all_in_of_list_u_not_in_of_list_t.
smt().
qed.

(* not needed?
lemma step_compare_iff (t : term, i j : int) :
  step t = Compare i j <=>
  (exists (n : int, u : term),
   t = Cons n u /\ step u = Compare i j) \/
  (exists (u v : term),
   t = Merge u v /\ step u = Compare i j) \/
  (exists (xs : int list, v : term),
   t = Merge (List xs) v /\ step v = Compare i j) \/
  (exists (u v : term), t = Cond i j u v).
proof.
case t.
smt().
smt().
move => n u.
split => [H | /#].
left; exists n u; smt().
move => u v.
split => [/= | /#].
case (is_worked (step u)) => [// | not_is_worked_u].
case (is_compare (step u)) =>
  [is_compare_u step_u_eq_Compare_i_j | not_is_compare_u].
left; by exists u v.
case (is_worked (step v)) => [// | not_is_worked_v].
case (is_compare (step v)) =>
  [is_compare_v step_u_eq_Compare_i_j | not_is_compare_v].
right.
have is_list_u : is_list u.
  move : not_is_worked_u not_is_compare_u.
  case u; smt().
have [xs ->] : exists xs, u = List xs.
  move : is_list_u.  
  clear not_is_worked_u not_is_compare_u.
  (case u; first smt()); last 3 smt().
  move => ys _; by exists ys.
by exists xs v.
smt().
smt().
qed.
*)

lemma step_worked_iff (t : term, i j : int) :
  step t = Worked u <=>
  (exists (xs : int list),
   
   t = List xs /\ 



  (exists (n : int, u : term),
   t = Cons n u /\ step u = Compare i j) \/
  (exists (u v : term),
   t = Merge u v /\ step u = Compare i j) \/
  (exists (xs : int list, v : term),
   t = Merge (List xs) v /\ step v = Compare i j) \/
  (exists (u v : term), t = Cond i j u v).
proof.
case t.



op answer (t : term, b : bool) : term option =
  with t = Sort xs      => None  (* should not happen *)
  with t = List xs      => None
  with t = Cons n u     =>
    let u' = answer t b in
    if u' = None  (* should not happen *)
    then None
    else Some (Cons n (oget u'))
  with t = Merge u v    =>
    let u' = answer u b in
    if u' <> None
    then Some (Merge (oget u') v)
    else (* u should be List ... *)
         let v' = answer v b in
         if v' = None
         then None  (* should not happen *)
         else Some (Merge u (oget v'))
  with t = Cond i j u v =>
    if b
    then Some (Cons i (Merge u (Cons j v)))
    else Some (Cons j (Merge (Cons i u) v).

op repr (cmp : int -> int -> bool, t : term) : int list =
  with t = Sort xs      => sort cmp xs
  with t = List xs      => xs
  with t = Cons i u     => i :: repr cmp u
  with t = Merge u v    => merge cmp (repr cmp u) (repr cmp v)
  with t = Cond i j u v =>
    if cmp i j
    then i :: merge cmp (repr cmp u)      (j :: repr cmp v)
    else j :: merge cmp (i :: repr cmp u) (repr cmp v).

lemma square_divide_lt (n : int) :
  2 <= n =>
  (n %/ 2) ^ 2 + (n %%/ 2) ^ 2 < n ^ 2.
proof.
admit.
qed.

(* termination metric for step *)

op metric (t : term) : int =
  with t = Sort xs      => size xs ^ 2
  with t = List xs      => 0
  with t = Cons i u     => metric u + 1
  with t = Merge u v    => 1 + metric u + metric v
  with t = Cond i j u v => 0.

(* here is our algorithm: *)

module Alg : ALG = {
  var term : term

  proc init(aux : aux) : unit = {
    term <- Sort range_len;
  }

  proc make_query_or_report_output() : response = {
    var r : response;
    var step : step;
    var don : bool <- false;
    while (!don) {
      step <- step term;
      if (step = Done \/ is_compare step) {
        don <- true;
      }
      else {
        term <- of_step step;
      }
    }
    if (step = Done) {  (* term = List ... *)
      r <- Response_Report (of_list term);
    }
    else {
      r <- Response_Query (enc (of_compare step));
    }
    return r;
  }

  proc query_result(b : inp) : unit = {
    term <- oget (answer term b);
  }
}.

(* algorithm is lossless *)

lemma Alg_init_ll : islossless Alg.init.
proof.
proc; auto.
qed.

lemma Alg_make_query_or_report_output_ll :
  islossless Alg.make_query_or_report_output.
proof.
proc.
admit.  (* will need termination metric for while loop *)
qed.

lemma Alg_query_result_ll :
  islossless Alg.query_result.
proof.
proc; auto.
qed.
