(* integer logarithm *)

require import AllCore StdOrder IntDiv.
import IntOrder.

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

(* integer logarithm *)

op int_log (b n : int) : int =
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
