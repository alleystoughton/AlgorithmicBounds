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

require import SortingProb.  (* comparison-based sorting problem *)

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

    if (size inpss_t <= size inpss_f) {   (* answering false keeps as least *)
      inpss <- filter_nth inpss i false;  (* as many inputs lists as *)
      ret <- false;                       (* answering true *)
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
smt(filter_nth_size_b_not_b).
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
  forall (Alg <: ALG{Adv}) (alg_term_invar : (glob Alg) -> bool),
  phoare
  [Alg.init : true ==> alg_term_invar (glob Alg)] = 1%r =>
  phoare
  [Alg.make_query :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r =>
  phoare
  [Alg.query_result :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r =>
  Pr[G(Alg, Adv).main() @ &m : res.`1 \/ bound <= res.`2] = 1%r.
proof.
move => le_bound_ilu2_fact_len.
exists Adv.
split; first apply Adv_init_ll.
split; first apply Adv_ans_query_ll.
move =>
  Alg alg_term_invar Alg_init_term Alg_make_query_term Alg_query_result_term.
byphoare => //.
conseq
  (_ : true ==> true)
  (_ : true ==> res.`1 \/ bound <= res.`2) => //.
apply (G_Adv_main bound Alg) => //.
rewrite (G_ll Alg Adv alg_term_invar predT)
        1:Alg_init_term 1:Alg_make_query_term 1:Alg_query_result_term
        1:Adv_init_ll Adv_ans_query_ll.
qed.

lemma int_log2_eq_1 : int_log 2 2 = 1.
proof.
by rewrite eq_sym (int_logPuniq 2 2 1) // expr1 /= expr2.
qed.

lemma int_log_geq (x b n : int) :
  0 <= x => 2 <= b => 1 <= n =>  b ^ x <= n => x <= int_log b n.
proof.
move => ge0_x ge2_b ge1_n le_pow_b_x_n.
rewrite -(int_log_pow_b b x) //= int_log_le //= exprn_ege1 //= 1:/#.
qed.

lemma div2_le_if_le_tim2_plus1 (n m : int) :
  n <= m * 2 + 1 => n %/ 2 <= m.
proof.
move => le_n_m_tim2_plus1.
rewrite (ler_trans ((m * 2 + 1) %/ 2)).
by rewrite leq_div2r.  
by rewrite div_succ_eq // 1:-even_iff_plus1_odd 1:dvdz_mull // mulzK.
qed.

lemma log_fact_helper (n : int) :
  0 <= n => 1 <= n =>
  n * (int_log 2 n + 2) <= (int_log 2 (fact n) + 2 ^ int_log 2 n) * 2 + 1.
proof.    
elim n => [le1_0 /# | n ge0_n ih].   
move : ge0_n.  
case (2 < n) => [gt2_n _ _ | le2_n ge0_n _].
(* 2 < n *)
have lb1 : 2 <= int_log 2 (n + 1) by rewrite int_log_geq // 1:/# expr2 /#.
have lb2 : int_log 2 (n + 1) + int_log 2 (fact n) <= int_log 2 (fact(n + 1))
  by rewrite factS // 1:/# int_log_distr_mul_lb // 1:/#; smt(ge1_fact).       
have [e | [e1 e2]] :
  int_log 2 (n + 1) = int_log 2 n \/
  int_log 2 (n + 1) = (int_log 2 n) + 1 /\ 2 ^ (int_log 2 (n + 1)) = n + 1.
  have h4 : int_log 2 (n + 1) <= (int_log 2 n) + 1
    by rewrite (ge2_exp_le_equiv 2 (int_log 2 (n + 1)) ((int_log 2 n) + 1)) //;
    smt(int_log_lb_le int_log_ub_lt int_log_ge0).
  rewrite lez_eqVlt in h4.
  elim h4 => [h5 //= | //=].
  right; split; smt(int_log_lb_le int_log_ub_lt). 
  rewrite ltzS lez_eqVlt => [#] [eq_log | neq_log].  
  by left.
  have neq_log2: 2 ^ (int_log 2 (n + 1) + 1) <= 2 ^ (int_log 2 n) 
    by rewrite -(ge2_exp_le_equiv 2 ((int_log 2 (n + 1)) + 1 ) (int_log 2 n))
               //=; smt(int_log_ge0).
  (* contradiction: n + 1 < n *)
  smt(int_log_le).   
rewrite e mulzDl.
have lb :
  n * (int_log 2 n + 2) + (int_log 2 n + 2) <=
  (int_log 2 (fact n) + 2 ^ int_log 2 n) * 2 + 1 + (int_log 2 n * 2)
  by rewrite ler_add 1:ih // 1://# mul2r -e //#. 
rewrite
  (lez_trans ((int_log 2 (fact n) + 2 ^ int_log 2 n) * 2 + 1 + int_log 2 n * 2))
  // addzC.
have -> //= /# :
  int_log 2 n * 2 + ((int_log 2 (fact n) + 2 ^ int_log 2 n) * 2 + 1) =
  (int_log 2 n + int_log 2 (fact n) + 2 ^ int_log 2 n) * 2 + 1 by smt().
rewrite e1 mulzDl.   
have -> :
  n * (int_log 2 n + 1 + 2) + 1 * (int_log 2 n + 1 + 2) =
  n * (int_log 2 n + 2) + (int_log 2 n + 3 + n) by smt().
have lb :
  n * (int_log 2 n + 2) +  (int_log 2 n + 3 + n) <=
  (int_log 2 (fact n) + 2 ^ int_log 2 n) * 2 + 1 + (int_log 2 n + 3 + n)
  by smt(ler_add).     
rewrite
  (lez_trans ((int_log 2 (fact n) + 2 ^ int_log 2 n) * 2 +
              1 + (int_log 2 n + 3 + n)))
  // -e1 e2 mulzDl.             
have -> /# : 2 ^ (int_log 2 n) * 2 = 2 ^ (int_log 2 n + 1)
  by rewrite exprS 1:int_log_ge0 //= 1:/# /#.
(* n <= 2 *)  
rewrite -lerNgt in le2_n.
have [eq0_n //= | [eq1_n | eq2_n]] : n = 0 \/ n = 1 \/ n = 2 by smt().
(* n = 0 *)
rewrite eq0_n (fact1 0) //=. 
have -> //= : int_log 2 1 = 0 by smt(int_log1_eq0).
smt(expr0).
(* n = 1 *)                  
rewrite eq1_n //=.
have -> : fact 2 = 2 by smt(factS fact1 fact0 expr1).
rewrite int_log2_eq_1; smt(expr1).                  
(* n = 2 *)
rewrite eq2_n //=.
have -> : fact 3 = 2 * 3 by smt(factS fact1 fact0 expr1).
have int_log2_3_eq_1 : 1 = int_log 2 3
  by rewrite (int_logPuniq 2 3 1) //=; smt(expr1 exprS).
smt(int_log_distr_mul_lb int_log2_eq_1 expr1).
qed.

lemma log2_fact_aux (n : int) :
   1 <= n => n * int_log 2 n <= int_log 2 (fact n) * 2 + 1.
proof.
smt(int_log_lb_le log_fact_helper).
qed.

lemma log2_fact (n : int) :
  1 <= n => (n * int_log 2 n) %/ 2 <= int_log 2 (fact n). 
proof.
move => ge1_n.
by rewrite div2_le_if_le_tim2_plus1 log2_fact_aux.
qed.

lemma int_log_leq_plus1 (b n : int) :
  1 <= n => 2 <= b => int_log b (n + 1) <= int_log b n + 1.
proof.
move => ge1_n ge2_b.    
case (int_log b (n + 1) = int_log b n) => [//# | not_eq].
rewrite (ge2_exp_le_equiv b (int_log b (n + 1)) ((int_log b n) + 1)) //=;
smt(int_log_ge0 int_log_lb_le int_log_ub_lt).
qed.

lemma log2_fact_precise (n : int) :
  0 <= n => 1 <= n =>
  n * (int_log 2 n) - 2 * 2 ^ (int_log 2 n) <= int_log 2 (fact n).
proof.
elim n => [| i ge0_i ih _].
rewrite fact0 //=. 
case (0 = i) => [//= | neq0_i]; first progress; smt(fact1 int_log1_eq0 expr0).
have ge1_i : 1 <= i by smt().
have e1 : int_log 2 (i + 1) <= (int_log 2 i) + 1 by smt(int_log_leq_plus1).
have e2 : (i + 1) * int_log 2 (i + 1) <= (i + 1) * ((int_log 2 i) + 1)
  by rewrite ler_wpmul2l /#. 
have e3 : int_log 2 (fact i) + int_log 2 (i + 1) <= int_log 2 (fact (i + 1))
  by rewrite factS //; smt(int_log_distr_mul_lb ge1_fact).
case (int_log 2 i = int_log 2 (i + 1)) => [eq_log | not_eq //].
(* int_log 2 i = int_log 2 (i + 1) *)
rewrite -eq_log; smt(lez_trans).
(* 1 + int_log 2 i = int_log 2 (i + 1) *)
rewrite (lez_trans ((int_log 2 (fact i)) + (int_log 2 (i + 1)))) //=.
have <- : (int_log 2 i) + 1 = int_log 2 (i + 1)
  by smt(int_log_leq_plus1 int_log_le).
have -> :
  (i + 1) * (int_log 2 i + 1) = i * (int_log 2 i) + (int_log 2 i) + i + 1
  by smt().
smt(lez_trans int_log_ub_lt exprS int_log_ge0 int_log_ub_lt). 
qed. 

lemma int_log16_eq_4 : int_log 2 16 = 4.
proof.
rewrite eq_sym (int_logPuniq 2 16 4) //.
smt(expr1 expr2 exprS).
qed.

lemma conditional_precise_ge16 (n : int) :
  16 <= n =>
  (n * int_log 2 n) %/ 2 <= n * (int_log 2 n) - 2 * 2 ^ (int_log 2 n).
proof.
move => ge16_n.
have /# :
  2 * 2 ^ (int_log 2 n) <= n * (int_log 2 n) - n * (int_log 2 n) %/ 2.
  rewrite (lez_trans (n * int_log 2 n %/ 2)) 2:/#.
  have e : 2 ^ int_log 2 n <= n by smt(int_log_lb_le).
  rewrite (lez_trans (2 * n)) 1:/#. 
  have bound : 2 <= (int_log 2 n) %/ 2 by smt(int_log_le int_log16_eq_4).
  rewrite -(ler_pmul2l n) in bound; smt(). 
qed.

lemma conditional_precise_ge11 (n : int) :
  11 <= n =>
  (n * int_log 2 n) %/ 2 <= n * (int_log 2 n) - 2 * 2 ^ (int_log 2 n).
proof.
admit.
qed.

(* below are several versions of our main theorem, for two
   lower-approximations of our target (int_log_up (fact len)),
   plus our target itself *)

(* first approximation: (len * int_log 2 len %/ 2) *)

lemma lower_bound_approx &m :
  exists (Adv <: ADV),
  islossless Adv.init /\ islossless Adv.ans_query /\
  forall (Alg <: ALG{Adv}) (alg_term_invar : (glob Alg) -> bool),
  phoare
  [Alg.init : true ==> alg_term_invar (glob Alg)] = 1%r =>
  phoare
  [Alg.make_query :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r =>
  phoare
  [Alg.query_result :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r =>
  Pr[G(Alg, Adv).main() @ &m :
       res.`1 \/ len * int_log 2 len %/ 2 <= res.`2] = 1%r.
proof.
apply (lower_bound_gen (len * int_log 2 len %/ 2) &m _).
rewrite (ler_trans (int_log 2 (fact len))).
rewrite log2_fact ge1_len.
rewrite int_log_int_log_up_le.
qed.

(* second approximation: len * (int_log 2 len) - 2 * 2 ^ (int_log 2 len)

   as proved above, as long as 11 <= len, the second approximation
   is >= the first one *)

lemma lower_bound_precise_approx &m :
  exists (Adv <: ADV),
  islossless Adv.init /\ islossless Adv.ans_query /\
  forall (Alg <: ALG{Adv}) (alg_term_invar : (glob Alg) -> bool),
  phoare
  [Alg.init : true ==> alg_term_invar (glob Alg)] = 1%r =>
  phoare
  [Alg.make_query :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r =>
  phoare
  [Alg.query_result :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r =>
  Pr[G(Alg, Adv).main() @ &m :
       res.`1 \/
       len * (int_log 2 len) - 2 * 2 ^ (int_log 2 len) <= res.`2] = 1%r.
proof.
apply
  (lower_bound_gen
   (len * (int_log 2 len) - 2 * 2 ^ (int_log 2 len))
   &m _).
rewrite (ler_trans (int_log 2 (fact len))).
by rewrite log2_fact_precise 1:ge0_len ge1_len.
rewrite int_log_int_log_up_le.
qed.

(* target : int_log_up 2 (fact len) *)

lemma lower_bound_target &m :
  exists (Adv <: ADV),
  islossless Adv.init /\ islossless Adv.ans_query /\
  forall (Alg <: ALG{Adv}) (alg_term_invar : (glob Alg) -> bool),
  phoare
  [Alg.init : true ==> alg_term_invar (glob Alg)] = 1%r =>
  phoare
  [Alg.make_query :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r =>
  phoare
  [Alg.query_result :
   alg_term_invar (glob Alg) ==> alg_term_invar (glob Alg)] = 1%r =>
  Pr[G(Alg, Adv).main() @ &m :
       res.`1 \/ int_log_up 2 (fact len) <= res.`2] = 1%r.
proof.
by apply (lower_bound_gen (int_log_up 2 (fact len)) &m _).
qed.

(* for comparison, here is a table showing the exact values of the two
   lower-approximations and the target as len ranges from 1 to 100:

   len   first   second   target
   -----------------------------
    1:       0       -2        0
    2:       1       -2        1
    3:       1       -1        3
    4:       4        0        5
    5:       5        2        7
    6:       6        4       10
    7:       7        6       13
    8:      12        8       16
    9:      13       11       19
   10:      15       14       22
   11:      16       17       26
   12:      18       20       29
   13:      19       23       33
   14:      21       26       37
   15:      22       29       41
   16:      32       32       45
   17:      34       36       49
   18:      36       40       53
   19:      38       44       57
   20:      40       48       62
   21:      42       52       66
   22:      44       56       70
   23:      46       60       75
   24:      48       64       80
   25:      50       68       84
   26:      52       72       89
   27:      54       76       94
   28:      56       80       98
   29:      58       84      103
   30:      60       88      108
   31:      62       92      113
   32:      80       96      118
   33:      82      101      123
   34:      85      106      128
   35:      87      111      133
   36:      90      116      139
   37:      92      121      144
   38:      95      126      149
   39:      97      131      154
   40:     100      136      160
   41:     102      141      165
   42:     105      146      170
   43:     107      151      176
   44:     110      156      181
   45:     112      161      187
   46:     115      166      192
   47:     117      171      198
   48:     120      176      203
   49:     122      181      209
   50:     125      186      215
   51:     127      191      220
   52:     130      196      226
   53:     132      201      232
   54:     135      206      238
   55:     137      211      243
   56:     140      216      249
   57:     142      221      255
   58:     145      226      261
   59:     147      231      267
   60:     150      236      273
   61:     152      241      279
   62:     155      246      285
   63:     157      251      290
   64:     192      256      296
   65:     195      262      303
   66:     198      268      309
   67:     201      274      315
   68:     204      280      321
   69:     207      286      327
   70:     210      292      333
   71:     213      298      339
   72:     216      304      345
   73:     219      310      351
   74:     222      316      358
   75:     225      322      364
   76:     228      328      370
   77:     231      334      376
   78:     234      340      383
   79:     237      346      389
   80:     240      352      395
   81:     243      358      402
   82:     246      364      408
   83:     249      370      414
   84:     252      376      421
   85:     255      382      427
   86:     258      388      434
   87:     261      394      440
   88:     264      400      447
   89:     267      406      453
   90:     270      412      459
   91:     273      418      466
   92:     276      424      473
   93:     279      430      479
   94:     282      436      486
   95:     285      442      492
   96:     288      448      499
   97:     291      454      505
   98:     294      460      512
   99:     297      466      519
  100:     300      472      525

And here are the results for three larger values of len:

       len      first      second      target
   ------------------------------------------
      1000:      4500        7976        8530
     10000:     65000      113616      118459
     20000:    140000      247232      256909

- - - - -

If we want to compare our lower- and upper bound results for sorting,
it's most precise to compare the greatest lower bound

(1) int_log_up 2 (fact len)

with the least upper bound

(2) wc len

Below is a table showing how these values are related as
len ranges from 1 to 19:

   len    (1)     (2)
   ------------------
    1:      0       0
    2:      1       1
    3:      3       3
    4:      5       5
    5:      7       8
    6:     10      11
    7:     13      14
    8:     16      17
    9:     19      21
   10:     22      25
   11:     26      29
   12:     29      33
   13:     33      37
   14:     37      41
   15:     41      45
   16:     45      49
   17:     49      54
   18:     53      59
   19:     57      64

Note that they are equal for the first four values of len. *)

