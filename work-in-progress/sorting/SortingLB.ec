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
  
lemma log2_fact_aux (n : int) :
   1 <= n => n * int_log 2 n <= int_log 2 (fact n) * 2 + 1.
proof.
have helper :
  0 <= n => 1 <= n =>
  n * (int_log 2 n +2) <= (int_log 2 (fact n)  + 2 ^ int_log 2 n) * 2 + 1.
  elim n => [| n ge0_n ih ]. 
  smt( fact0 int_log_ge0  expr0).    
  move : ge0_n.  
  case (2 < n) => [ gt2_n _ _ | leq2_n ge0_n _].
  (*2 < n*)
  have :
    int_log 2 (n+1) = int_log 2 n \/
    int_log 2 (n+1) = (int_log 2 n) + 1 /\ 2 ^(int_log 2 (n+1)) = n + 1.
    have e1: 2 ^(int_log 2 n) <= n by rewrite int_log_lb_le //#.
    have e2: n < 2^((int_log 2 n) +1 ) by rewrite int_log_ub_lt //#. 
    have e3: 2 ^(int_log 2 (n+1)) <= n+1 by rewrite int_log_lb_le //#.
    have e4: (int_log 2 (n+1)) <= (int_log 2 n ) +1
    by rewrite (ge2_exp_le_equiv 2 ( int_log 2 (n+1) ) ((int_log 2 n ) +1 ) ) //= ; smt(int_log_ge0).
    rewrite lez_eqVlt in e4.
    elim e4 => [ e5 //= | //=].
    right ; split => //#.
    rewrite ltzS lez_eqVlt => [#]  [eq_log | neq_log ].  
    by left.
    have neq_log2: (int_log 2 (n+1)) + 1 <= int_log 2 n by  smt().  
      rewrite (ge2_exp_le_equiv 2 ( (int_log 2 (n+1)) +1 ) (int_log 2 n)  ) // in neq_log2.
      smt(int_log_ge0). smt(int_log_ge0).
    (*contradiction: n +1 < n*)
    smt(int_log_ub_lt).
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
  have -> :  2 ^ (int_log 2 n) * 2 = 2 ^ (int_log 2 n + 1) by  rewrite exprS 1:int_log_ge0 //= 1:/# /#.
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
  smt(int_log_distr_mul_lb int_log2_eq_1 expr1).   
smt(int_log_lb_le).
qed.

lemma log2_fact (n: int) :
  1 <= n => (n * (int_log 2 n )) %/ 2 <= int_log 2 (fact n). 
proof.
move => ge1_n.
by rewrite div2_le_if_le_tim2_plus1 log2_fact_aux.
qed.

lemma int_log_leq_plus1 (b n: int) :
  1 <= n => 2 <= b =>  int_log b (n+1) <= (int_log b n) +1.
proof.
move => ge1_n ge2_b.    
case (int_log b (n +1) = int_log b n) => [ //# | not_eq ].
rewrite (ge2_exp_le_equiv b ( int_log b (n+1)  ) ((int_log b n) +1)  ) //=.
smt(int_log_ge0). smt(int_log_ge0).
smt(int_log_lb_le int_log_ub_lt).
qed.

lemma log2_fact_precise (n : int) :
     0<=n => 1<=n => n* (int_log 2 n) - 2*2^(int_log 2 n) <= int_log 2 (fact n).
proof.
  elim n. rewrite fact0 //=. 
move => i ge0_i  ih _.
case (0= i) => [ //= |neq0_i ]. progress; smt(fact1 int_log1_eq0 expr0).
have ge1_i : 1 <= i  by smt().
have e: int_log 2 i <= int_log 2 (i+1) by rewrite int_log_le //#.
have e1 : int_log 2 (i+1) <= (int_log 2 i) + 1 by smt(int_log_leq_plus1).
have e2: (i + 1) * int_log 2 (i + 1)  <= (i + 1) * ( (int_log 2 i) + 1) by rewrite ler_wpmul2l; smt(). 
(* search (_ <=_ => _*_<=_*_ )%Int .  *)
have e3: (i + 1) * int_log 2 (i + 1) - (i+1)  <= (i + 1) * ( (int_log 2 i) ) by smt().
have e5: fact(i+1) = fact i * (i+1) by smt(factS).
have e4:   int_log 2 (fact (i )) + int_log 2 (i+1)<= int_log 2 (fact (i + 1)) by
  smt(factS int_log_distr_mul_lb addzC fact0 ge1_fact).
case (int_log 2 i = int_log 2 (i+1)) => [ eq_log | not_eq //].
(* int_log 2 i = int_log 2 (i+1) *)
rewrite -eq_log. 
smt(lez_trans).
(* 1 + int_log 2 i = int_log 2 (i+1) *)
have e6:  i * int_log 2 i - 2 * 2 ^ int_log 2 i <= int_log 2 (fact i) by smt().
rewrite (lez_trans ( (int_log 2 (fact i)) + ( int_log 2 (i + 1)) ) ) //= .
have <- :(int_log 2 i)+1 = int_log 2 (i+1) by smt(int_log_leq_plus1).
have -> : (i + 1) * (int_log 2 i + 1) = i*(int_log 2 i) + (int_log 2 i)+ i + 1 by smt().
  (* have e8 : i <=  2 ^ (int_log 2 i + 1) by smt(int_log_ub_lt). *)
  (*  have e9: 2 * 2 ^ (int_log 2 i + 1) *)
  (*  - 2 * 2 ^ (int_log 2 i ) =  2 ^ (int_log 2 i + 1) by smt(exprS int_log_ge0). *)
smt(lez_trans int_log_ub_lt exprS int_log_ge0 int_log_ub_lt ). 
qed. 


(* here our main theorem: *)

lemma lower_bound &m :
  exists (Adv <: ADV),
  islossless Adv.init /\ islossless Adv.ans_query /\
  forall (Alg <: ALG{Adv}),
  islossless Alg.init => islossless Alg.make_query =>
  islossless Alg.query_result =>
  Pr[G(Alg, Adv).main() @ &m :
       res.`1 \/ len * int_log 2 len %/ 2 <= res.`2] = 1%r.
proof.
apply (lower_bound_gen (len * int_log 2 len %/ 2) &m _).
rewrite (ler_trans (int_log 2 (fact len))).
rewrite log2_fact ge1_len.
rewrite int_log_int_log_up_le.
qed.
