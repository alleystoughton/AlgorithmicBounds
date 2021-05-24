(* integer logarithms - both rounding down (default) and rounding
   up *)

prover [""].  (* no use of SMT provers *)

require import AllCore StdOrder IntDiv.
import IntOrder.

(* rounding down integer logarithm (default) *)

lemma exists_int_log (b n : int) :
  2 <= b => 1 <= n =>
  exists (k : int), 0 <= k /\ b ^ k <= n < b ^ (k + 1).
proof.
move => ge2_b ge1_n.
have gt1_b : 1 < b by rewrite ltzE.
have gt0_b : 0 < b by rewrite (ltr_trans 1).
have ge0_b : 0 <= b by rewrite ltrW.
have H :
  forall n,
  0 <= n => 1 <= n =>
  exists (k : int), 0 <= k /\ b ^ k <= n < b ^ (k + 1).
  apply sintind => i ge0_i IH /= ge1_i.
  case (i < b) => [lt_i_b | ge_b_i].
  exists 0; by rewrite /= expr0 ge1_i /= expr1.
  rewrite -lerNgt in ge_b_i.
  have [ge1_i_div_b i_div_b_lt_i] : 1 <= i %/ b < i.
    split => [| _].
    by rewrite lez_divRL 1:gt0_b.
    by rewrite ltz_divLR 1:gt0_b -divr1 mulzA 1:ltr_pmul2l ltzE.
  have /= [k [#] ge0_k b_exp_k_le_i_div_b i_div_b_lt_b_tim_b_exp_k]
       := IH (i %/ b) _ _.
    split; [by rewrite (lez_trans 1) | trivial].
    trivial.
  rewrite exprS // in i_div_b_lt_b_tim_b_exp_k.
  exists (k + 1).
  split; first by rewrite ler_paddl.
  rewrite exprS // mulzC exprS 1:ler_paddr // exprS //.
  split => [| _].
  rewrite (lez_trans ((i %/ b) * b)).
  by rewrite ler_wpmul2r 1:(lez_trans 2).
  by rewrite leq_trunc_div 1:(lez_trans 1).
  rewrite ltz_divLR // in i_div_b_lt_b_tim_b_exp_k.
  by rewrite mulzC.
by rewrite H (lez_trans 1).
qed.

lemma int_log_uniq (b n k1 k2 : int) :
  2 <= b =>
  0 <= k1 => b ^ k1 <= n => n < b ^ (k1 + 1) =>
  0 <= k2 => b ^ k2 <= n => n < b ^ (k2 + 1) =>
  k1 = k2.
proof.
move => ge2_b ge0_k1 b2k1_le_n n_lt_b2k1p1 ge0_k2 b2k2_le_n n_lt_b2k2p1.
have ge1_b : 1 <= b.
  by rewrite (lez_trans 2).
case (k1 = k2) => [// | /ltr_total [lt_k1_k2 | lt_k2_k1]].
rewrite ltzE in lt_k1_k2.
have b2k1p1_le_b2k2 : b ^ (k1 + 1) <= b ^ k2.
  by rewrite ler_weexpn2l // lt_k1_k2 /= addr_ge0.
have // : n < n.
  by rewrite (ltr_le_trans (b ^ (k1 + 1))) // (lez_trans (b ^ k2)).
rewrite ltzE in lt_k2_k1.
have b2k2p1_le_b2k1 : b ^ (k2 + 1) <= b ^ k1.
  by rewrite ler_weexpn2l // lt_k2_k1 /= addr_ge0.
have // : n < n.
  by rewrite (ltr_le_trans (b ^ (k2 + 1))) // (lez_trans (b ^ k1)).
qed.

(* integer logarithm (should not be applied when b <= 1 or n <= 0) *)

op nosmt int_log (b n : int) : int =
  choiceb
  (fun (k : int) => 0 <= k /\ b ^ k <= n < b ^ (k + 1))
  0.

lemma int_logP (b n : int) :
  2 <= b => 1 <= n =>
  0 <= int_log b n /\ b ^ (int_log b n) <= n < b ^ (int_log b n + 1).
proof.
move => ge2_b ge1_n.
have // := choicebP (fun k => 0 <= k /\ b ^ k <= n < b ^ (k + 1)) 0 _.
  by rewrite /= exists_int_log.
qed.

lemma int_log_ge0 (b n : int) :
  2 <= b => 1 <= n => 0 <= int_log b n.
proof.
move => ge2_b ge1_n.
have := int_logP b n _ _ => //.
qed.

lemma int_log_lb_le (b n : int) :
  2 <= b => 1 <= n => b ^ (int_log b n) <= n.
proof.
move => ge2_b ge1_n.
have := int_logP b n _ _ => //.
qed.

lemma int_log_up_lt (b n : int) :
  2 <= b => 1 <= n => n < b ^ (int_log b n + 1).
proof.
move => ge2_b ge1_n.
have := int_logP b n _ _ => //.
qed.

lemma int_logPuniq (b n l : int) :
  2 <= b =>
  0 <= l => b ^ l <= n < b ^ (l + 1) =>
  l = int_log b n.
proof.
move => ge2_b ge0_n [b2l_le_n n_lt_b2lp1].
have ge1_n : 1 <= n.
  by rewrite (lez_trans (b ^ l)) // exprn_ege1 // (lez_trans 2).
have := int_logP b n _ _ => // [#] ge0_il b2il_le_n n_lt_b2ilp1.
by apply (int_log_uniq b n).
qed.

(* integer logarithm rounding up (should not be applied when b <= 1 or
   n <= 0) *)

op nosmt int_log_up (b n : int) : int =
  int_log b n + ((b ^ int_log b n = n) ? 0 : 1).

lemma int_log_upP (b n : int) :
  2 <= b => 1 <= n =>
  (int_log_up b n = 0 /\ n = 1 \/
   1 <= int_log_up b n /\
   b ^ (int_log_up b n - 1) < n <= b ^ (int_log_up b n)).
proof.
move => ge2_b ge1_n.
rewrite /int_log_up.
have [#] ge0_il b2il_le_n n_lt_b2ilp1 := int_logP b n _ _ => //.
case (int_log_up b n = 0) => [eq0_ilu | ne0_ilu].
rewrite /int_log_up in eq0_ilu.
left.
rewrite eq0_ilu /=.
have eq_b2il_n : b ^ int_log b n = n.
  case (b ^ int_log b n = n) => [// | ne_b2il_n].
  move : eq0_ilu.
  by rewrite ne_b2il_n /= addz1_neq0.
have eq0_il : int_log b n = 0.
  move : eq0_ilu.
  by rewrite eq_b2il_n.
move : eq_b2il_n.
by rewrite eq0_il expr0.
rewrite /int_log_up in ne0_ilu.
right.
case (b ^ int_log b n = n) => [eq_b2il_n | ne_b2il_n].
move : ne0_ilu.
rewrite eq_b2il_n /= => ne0_il.
have ge1_il : 1 <= int_log b n.
  rewrite -lt0n // -lez_add1r // in ne0_il.
split => //.
rewrite eq_b2il_n /=.
have [p] [ge0_p eq_il_p_plus1]
     : exists p, 0 <= p /\ int_log b n = p + 1.
  exists (int_log b n - 1).
  by rewrite /= subr_ge0.
rewrite eq_il_p_plus1 /= -eq_b2il_n ltz_def.
split.
case (b ^ int_log b n = b ^ p) => [eq_b2il_b2p | //].
have eq_il_p : int_log b n = p.
  rewrite (ieexprIn b _ _ (int_log b n) p) // 1:(ltr_le_trans 2) //.
by rewrite eq_sym ltr_eqF 1:(ltr_le_trans 2).
move : eq_il_p_plus1; rewrite eq_il_p => eq_p_p_plus1.
have // : 0 = 1.
  have -> : 0 = p - p by trivial.
  have -> // : 1 = p - p by rewrite {1}eq_p_p_plus1 //; algebra.
rewrite ler_weexpn2l 1:(ler_trans 2) // ge0_p /=.
by rewrite eq_il_p_plus1 ler_addl.
split => [| /=].
by rewrite -subr_ge0.
split => [// | _].
by rewrite ltz_def eq_sym.
by rewrite ltrW.
qed.

lemma int_log_up_ge0 (b n : int) :
  2 <= b => 1 <= n => 0 <= int_log_up b n.
proof.
move => ge2_b ge1_n.
have [[->] | [ge1_il _]] := int_log_upP b n _ _ => //.
by rewrite (ler_trans 1).
qed.

lemma int_log_up_zero_iff (b n : int) :
  2 <= b => 1 <= n =>
  int_log_up b n = 0 <=> n = 1.
proof.
move => ge2_b ge1_n.
have [// | [#] ge1_il lt_b2ilmin1_n _] := int_log_upP b n _ _ => //.
split => [eq0_il | eq1_n].
have // : 1 <= 0 by rewrite (ler_trans (int_log_up b n)) // eq0_il.
have : b ^ (int_log_up b n - 1) = 0.
  rewrite eqr_le.
  split => [| _].
  by rewrite -ltzS /= -{2}eq1_n.
  rewrite expr_ge0 (ler_trans 2) //.
rewrite expf_eq0 => [[_ eq0_b]].
have // : 2 <= 0 by rewrite (ler_trans b) // eq0_b.
qed.

lemma int_log_up_nonzero_ge1 (b n : int) :
  2 <= b => 2 <= n => 1 <= int_log_up b n.
proof.
move => ge2_b ge2_n.
have [[_ eq1_n] |] := int_log_upP b n _ _ => //.
  by rewrite (ler_trans 2).
have // : 2 <= 1 by rewrite -eq1_n.
qed.

lemma int_log_up_nonzero_lb_lt (b n : int) :
  2 <= b => 2 <= n => b ^ (int_log_up b n - 1) < n.
proof.
move => ge2_b ge2_n.
have [[_ eq1_n] |] := int_log_upP b n _ _ => //.
  by rewrite (ler_trans 2).
have // : 2 <= 1 by rewrite -eq1_n.
qed.

lemma int_log_up_nonzero_ub_le (b n : int) :
  2 <= b => 2 <= n => n <= b ^ (int_log_up b n).
proof.
move => ge2_b ge2_n.
have [[_ eq1_n] |] := int_log_upP b n _ _ => //.
  by rewrite (ler_trans 2).
have // : 2 <= 1 by rewrite -eq1_n.
qed.

lemma int_log_up_uniq (b n k1 k2 : int) :
  2 <= b => 2 <= n =>
  1 <= k1 => b ^ (k1 - 1) < n <= b ^ k1 =>
  1 <= k2 => b ^ (k2 - 1) < n <= b ^ k2 =>
  k1 = k2.
proof.
move => ge2_b ge2_n.
move => ge1_k1 [lt_b2k1min1_n le_n_b2k1].
move => ge1_k2 [lt_b2k2min1_n le_n_b2k2].
have ge1_b : 1 <= b.
  by rewrite (lez_trans 2).
have ge0_k1 : 0 <= k1 by rewrite (ler_trans 1).
have ge0_k2 : 0 <= k2 by rewrite (ler_trans 1).
case (k1 = k2) => [// | /ltr_total [lt_k1_k2 | lt_k2_k1]].
have le_k1_k2min1 : k1 <= k2 - 1 by rewrite -ltzS.
have b2k1_le_b2k2min1 : b ^ k1 <= b ^ (k2 - 1)
  by rewrite ler_weexpn2l.
have // : n < n.
  by rewrite (ler_lt_trans (b ^ k1)) //
             (ler_lt_trans (b ^ (k2 - 1))).
have le_k2_k1min1 : k2 <= k1 - 1 by rewrite -ltzS.
have b2k2_le_b2k1min1 : b ^ k2 <= b ^ (k1 - 1).
  by rewrite ler_weexpn2l.
have // : n < n.
  by rewrite (ler_lt_trans (b ^ k2)) //
             (ler_lt_trans (b ^ (k1 - 1))).
qed.

lemma int_log_upPuniq (b n l : int) :
  2 <= b => 2 <= n =>
  1 <= l => b ^ (l - 1) < n <= b ^ l =>
  l = int_log_up b n.
proof.
move => ge2_b ge2_n ge1_l [ge1_b2l_min1 le_n_b2l].
have [[_ eq1_n] |] := int_log_upP b n _ _ => //.
  by rewrite (ler_trans 2).
have // : 2 <= 1 by rewrite -eq1_n.
pose l' := int_log_up b n.
move => [#] ge1_l' lt_b2l'min1_n le_n_b2l'.
by apply (int_log_up_uniq b n).
qed.
