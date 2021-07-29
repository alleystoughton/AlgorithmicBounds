(* definitions and lemmas about integer division by powers of two,
   rounding down and up, plus connection to integer logarithms,
   rounding down and up *)

prover [""].  (* no use of SMT provers *)

require import AllCore StdOrder IntDiv IntLog.
import IntOrder.

(* basic facts *)

lemma mul2r (x : int) :
  x * 2 = x + x.
proof.
have -> : 2 = ofint_id 2 by rewrite /ofint_id mulr2z.
by rewrite mul1r2z.
qed.

lemma mul2l (x : int) :
  2 * x = x + x.
proof.
by rewrite mulrC mul2r.
qed.

lemma ne0_mod2 (m : int) :
  m %% 2 <> 0 <=> m %% 2 = 1.
proof.
split => [ne0_m_mod2 | -> //].
have ge0_m_mod2 := modz_ge0 m 2 _ => //.
have lt2_m_mod2 := ltz_pmod m 2 _ => //.
have gt0_m_mod2 : 0 < m %% 2 by rewrite ltz_def.
rewrite ltzE /= in gt0_m_mod2.
move : lt2_m_mod2.
  have {2}-> : 2 = 1 + 1 by trivial.
  rewrite ltzS.
move => le1_m_mod2.
by apply ler_anti.
qed.

lemma ne1_mod2 (m : int) :
  m %% 2 <> 1 <=> m %% 2 = 0.
proof.
split => [| -> //]; by rewrite -ne0_mod2.
qed.

lemma even_iff_plus1_odd (m : int) :
  2 %| m <=> ! (2 %| (m + 1)).
proof. by rewrite -!oddP oddS oddPn. qed.

lemma odd_iff_plus1_even (m : int) :
  ! 2 %| m <=> (2 %| (m + 1)).
proof. by rewrite even_iff_plus1_odd. qed.

lemma div2_even_plus1 (m : int) :
  2 %| m => (m + 1) %/ 2 = m %/ 2.
proof.
move => two_dvdz_m.
by rewrite divzDl.
qed.

lemma div2_odd_plus1 (m : int) :
  ! 2 %| m => (m + 1) %/ 2 = m %/ 2 + 1.
proof.
rewrite even_iff_plus1_odd /= => two_dvdz_m_plus1.
have {2}-> : m = (m + 1) - 1 by trivial.
by rewrite (divzDl (m + 1)).
qed.

lemma int_div_ge0 (m d : int) :
  0 <= m => 1 <= d => 0 <= m %/ d.
proof.
move => ge0_m ge1_d.
by rewrite divz_ge0 1:(ltr_le_trans 1).
qed.

lemma int_div2_0or1_implies_eq0 (m : int) :
  0 <= m <= 1 => m %/ 2 = 0.
proof.
move => [ge0_m le1_m].
rewrite -divz_eq0 //.
split => [// | _]; by rewrite -ltzS in le1_m.
qed.

lemma int_div2_ge2_implies_ge1 (m : int) :
  2 <= m => 1 <= m %/ 2.
proof.
move => ge2_m.
have [p [ge0_p ->]] : exists p, 0 <= p /\ m = 2 + p.
  exists (m - 2); split; [by rewrite ler_subr_addr | algebra].
by rewrite divzDl //= ler_paddr 1:int_div_ge0.
qed.

lemma int_div2_lt_self_if_ge2 (m : int) :
  2 <= m => m %/ 2 < m.
proof.
move => ge2_m.
rewrite (ltz_divLR m m 2) //.
have -> : m * 2 = m + m by algebra.
by rewrite ltr_addl (ltr_le_trans 2).
qed.

lemma div_2n_eq_div_n_div_2 (m n : int) :
  0 <= m => 0 < n =>
  m %/ (n * 2) = m %/ n %/ 2.
proof.
move => ge0_m gt0_n.
have ne0_n_tim2 : n * 2 <> 0.
  by rewrite gtr_eqF 1:pmulr_lgt0.
rewrite {2}(divz_eq m (n * 2)).
have -> : m %/ (n * 2) * (n * 2) = m %/ (n * 2) * 2 * n.
  by rewrite -mulrA (mulrC 2).
rewrite divzMDl 1:gtr_eqF // 1:divzMDl //.
have -> // : m %% (n * 2) %/ n %/ 2 = 0.
  rewrite divz_small //.
  split => [| _].
  by rewrite divz_ge0 // modz_ge0 ne0_n_tim2.
  rewrite ltz_divLR // ger0_norm // (mulrC 2).
  rewrite -{2}(ger0_norm (n * 2)) 1:mulr_ge0 1:ltzW //.
  by rewrite ltz_mod ne0_n_tim2.
qed.

(* like m %/ d, but add 1 if non-zero remainder: *)

op (%%/) (m d : int) : int =
  m %/ d + ((d %| m) ? 0 : 1).

lemma int_div2_le_int_div2_up (m d : int) :
  m %/ d <= m %%/ d.
proof.
rewrite /(%%/).
case (d %| m) => [d_dvdz_m // | not_d_dvdz_m].
by rewrite ler_paddr.
qed.

lemma int_div2_up_eq0_implies_eq0 (m d : int) :
  0 %%/ 2 = 0.
proof. trivial. qed.

lemma int_div2_up_ge1_implies_ge1 (m d : int) :
  1 <= m => 1 <= m %%/ 2.
proof.
move => ge0_m; rewrite /(%%/).
case (2 %| m) => [two_dvdz_m /= | not_two_dvdz_m].
rewrite int_div2_ge2_implies_ge1.
case (m = 1) => [eq1_m | ne1_m].
move : two_dvdz_m.
by rewrite eq1_m.
by rewrite -ltzS -ltr_subl_addr /= ltz_def.
by rewrite ler_paddl 1:int_div_ge0 1:(ler_trans 1).
qed.

lemma int_div2_up_le_self (m : int) :
  0 <= m => m %%/ 2 <= m.
proof.
move => ge0_m; rewrite /(%%/).
case (2 %| m) => [two_dvdz_m /= | not_two_dvdz_m].
by rewrite leq_div.
have m_eq := divz_eq m 2.
have eq1_m_mod2 : m %% 2 = 1.
  by rewrite -ne0_mod2.
rewrite {2}m_eq ler_add.
have -> : m %/ 2 * 2 = m %/ 2 + m %/ 2 by algebra.
by rewrite ler_paddl 1:int_div_ge0.
by rewrite eq1_m_mod2.
qed.

lemma int_div2_up_le_self_if_ge2 (m : int) :
  2 <= m => m %%/ 2 < m.
proof.
move => ge2_m; rewrite /(%%/).
case (2 %| m) => [two_dvdz_m /= | not_two_dvdz_m].
by rewrite int_div2_lt_self_if_ge2.
have m_eq := divz_eq m 2.
have eq1_m_mod2 : m %% 2 = 1 by rewrite -ne0_mod2.
rewrite {2}m_eq eq1_m_mod2 ltr_add2r.
have -> : m %/ 2 * 2 = m %/ 2 + m %/ 2 by algebra.
rewrite ltr_spaddl // ltz_def int_div_ge0 1:(ler_trans 2) //=.
case (m %/ 2 = 0) => [eq0_m_div2 | //].
move : m_eq.
rewrite eq0_m_div2 /= eq1_m_mod2.
case (m = 1) => [eq1_m | //].
have // : 2 <= 1 by rewrite (ler_trans m) // eq1_m.
qed.

lemma le_div_rnd_up (m n d : int) :
  1 <= d => m <= n => m %%/ d <= n %%/ d.
proof.
move => ge1_d le_m_n; rewrite /(%%/).
case (d %| m) => [d_dvdz_m /= | not_d_dvdz_m].
case (d %| n) => [d_dvdz_n | not_d_dvdz_n] /=.
by rewrite leq_div2r // (ler_trans 1).
by rewrite (ler_trans (n %/ d)) 1:leq_div2r // 1:(ler_trans 1) //
           ler_paddr.
case (d %| n) => [d_dvdz_n | not_d_dvdz_n] /=.
rewrite addrC lez_add1r.
have lt_m_n : m < n.
  rewrite ltr_neqAle le_m_n /=.
  move : not_d_dvdz_m d_dvdz_n.
  case (m = n) => [-> // | //].
rewrite ltz_divRL // 1:(ltr_le_trans 1) //.
rewrite (ler_lt_trans m) 1:lez_floor //.
by rewrite ltr0_neq0 1:(ltr_le_trans 1).
by rewrite ler_add2r 1:leq_div2r // (ler_trans 1).
qed.

lemma dvdz_comp (m n l : int) :
  0 <= m => 0 < n => 0 < l => n %| m => l %| m %/ n =>
  (n * l) %| m.
proof.
move => ge0_m gt0_n gt0_l.
rewrite !dvdzP => [[q m_eq] [r m_div_n_eq]].
exists r; by rewrite (mulrC n) mulrA -m_div_n_eq m_eq 1:mulzK 1:gtr_eqF.
qed.

lemma divru_2n_eq_divru_n_divru_2 (m n : int) :
  0 <= m => 0 < n => m %%/ (n * 2) = m %%/ n %%/ 2.
proof.
move => ge0_m gt0_n; rewrite /(%%/).
case ((n * 2) %| m) => [n2_dvdz_m | not_n2_dvdz_m].
have m_n2_eq : m = m %/ (n * 2) * (n * 2).
  have eq_m_n2 := divz_eq m (n * 2).
  rewrite dvdzE in n2_dvdz_m.
  by rewrite n2_dvdz_m /= in eq_m_n2.
have -> /= : n %| m.
  rewrite m_n2_eq {2}(mulrC n) mulrA.
  rewrite dvdz_mull dvdzz.
rewrite div_2n_eq_div_n_div_2 //.
have -> // : 2 %| m %/ n.
  by rewrite m_n2_eq {2}(mulrC n) mulrA mulrC mulKz 1:gtr_eqF //
             dvdzE modzMl.
rewrite div_2n_eq_div_n_div_2 //.
case (n %| m) => [n_dvdz_m /= | not_n_dvdz_m].
case (2 %| m %/ n) => [two_dvdz_m_div_n | //].
have // : n * 2 %| m by rewrite dvdz_comp.
case (2 %| (m %/ n + 1)) =>
  [two_dvdz_m_div_n_plus1 /= | not_two_dvdz_m_div_n_plus1].
by rewrite div2_odd_plus1 1:odd_iff_plus1_even.
by rewrite div2_even_plus1 1:even_iff_plus1_odd.
qed.

(* integer division by power of two *)

op divpow2 (n k : int) : int =
  n %/ (2 ^ k).

lemma divpow2_ge0 (n k : int) :
  0 <= n => 0 <= k => 0 <= divpow2 n k.
proof.
move => ge0_n ge0_k.
by rewrite /divpow2 int_div_ge0 // exprn_ege1.
qed.

lemma divpow2_next_lt (n k : int) :
  1 <= n => 0 <= k => 1 <= divpow2 n k =>
  divpow2 n (k + 1) < divpow2 n k.
proof.
rewrite /divpow2 => ge1_n ge0_k ge1_dp2_n_k.
rewrite exprS // mulrC div_2n_eq_div_n_div_2 1:(ler_trans 1)
        // 1:expr_gt0 //.
case (n %/ 2 ^ k = 1) => [-> // | ne1_n_div_two2k].
have ge2_n_div_two2k : 2 <= n %/ 2 ^ k.
have {1}-> : 2 = 1 + 1 by trivial.
by rewrite -ltzE ltz_def.
by rewrite int_div2_lt_self_if_ge2.
qed.

lemma divpow2_le1_next_eq0 (n k : int) :
  1 <= n => 0 <= k => divpow2 n k <= 1 =>
  divpow2 n (k + 1) = 0.
proof.
rewrite /divpow2.
move => ge1_n ge0_k le1_dp2_n_k.
rewrite exprS // mulrC.
rewrite div_2n_eq_div_n_div_2 1:(ler_trans 1) // 1:expr_gt0 //.
have le0_n_div_two2k_div_2 : n %/ 2 ^ k %/ 2 <= 0.
  have -> : 0 = 1 %/ 2 by trivial.
  by rewrite leq_div2r.
apply lez_anti.
by rewrite le0_n_div_two2k_div_2 /= divz_ge0 // divz_ge0 // 1:expr_gt0 //
           (ler_trans 1).
qed.

lemma divpow2_eq1_int_log (n k : int) :
  1 <= n => 0 <= k => divpow2 n k = 1 =>
  k = int_log 2 n.
proof.
rewrite /divpow2 => ge1_n ge0_k eq1_dp2.
rewrite (int_logPuniq 2 n k) // exprS //.
split => [| _].
case (2 ^ k <= n) => [// |].
rewrite -ltzNge => n_lt_two2k.
have : n %/ 2 ^ k = 0.
  rewrite divz_small //.
  split => [| _].
  by rewrite (ler_trans 1).
  rewrite ltr_normr //; by left.
by rewrite eq1_dp2.
case (n < 2 * 2 ^ k) => [// |].
rewrite -lerNgt => two_time_two2k_le_n.
have := leq_div2r (2 ^ k) (2 * 2 ^ k) n _ _ => //.
  by rewrite expr_ge0.
rewrite mulzK 1:gtr_eqF 1:expr_gt0 // => le_2_n_div_two2k.
have // : 2 <= 1 by rewrite (ler_trans (n %/ (2 ^ k))) // eq1_dp2.
qed.

lemma divpow2_eq0_int_log_up_le (n k : int) :
  1 <= n => 0 <= k => divpow2 n k = 0 =>
  int_log_up 2 n <= k.
proof.
move => ge1_n ge0_k; rewrite /divpow2 => eq0_dp2_n_k.
have [[-> _ //] | [#] _ two2ilu_2n_min1_lt_n _]
     := int_log_upP 2 n _ _ => //.
have lt_n_two2k : n < 2 ^ k.
  rewrite -divz_eq0 1:expr_gt0 // in eq0_dp2_n_k.
  by elim eq0_dp2_n_k.
case (int_log_up 2 n <= k) => [// | lt_k_ilu_2_n].
rewrite lerNgt /= in lt_k_ilu_2_n.
have le_k_ilu_2_n_min1 : k <= int_log_up 2 n - 1 by rewrite -ltzS.
have // : n < n.
  rewrite (ltr_trans (2 ^ k)) //.
  by rewrite (ler_lt_trans (2 ^ (int_log_up 2 n - 1))) 1:ler_weexpn2l.
qed.

lemma divpow2_eq0_int_log_le (n k : int) :
  1 <= n => 0 <= k => divpow2 n k = 0 => int_log 2 n <= k.
proof.
move => ge1_n ge0_k eq0_dp2_n_k.
rewrite (ler_trans (int_log_up 2 n)) 1:(int_log_int_log_up_le).
by rewrite divpow2_eq0_int_log_up_le.
qed.

lemma divpow2_le1_int_log_le (n k : int) :
  1 <= n => 0 <= k => divpow2 n k <= 1 =>
  int_log 2 n <= k.
proof.
move => ge1_n ge0_k le1_dp2_n_k.
have ge0_dp2 : 0 <= divpow2 n k by rewrite divpow2_ge0 1:(ler_trans 1).
have [eq0_dp2 | eq1_dp2] : divpow2 n k = 0 \/ divpow2 n k = 1.
  case (divpow2 n k = 0) => [// | ne0_dp2_n_k /=].
  have ge1_dp2_n_k : 0 < divpow2 n k by rewrite ltz_def.
  rewrite ltzE /= in ge1_dp2_n_k.
  by apply ler_anti.
by rewrite divpow2_eq0_int_log_le.
by rewrite (divpow2_eq1_int_log n k).
qed.

lemma divpow2_ge2_lt_int_log (n k : int) :
  1 <= n => 0 <= k => 2 <= divpow2 n k =>
  k < int_log 2 n.
proof.
rewrite /divpow2 => ge1_n ge0_k dp2_n_k.
have lt_two2k_n : 2 ^ (k + 1) <= n.
  rewrite lez_divRL 1:expr_gt0 // in dp2_n_k.
  by rewrite exprS.
have [#] := int_logP 2 n _ _ => //.
pose il := int_log 2 n.
move => ge0_il le_two2il_n lt_n_two2_ilplus1.
case (k < il) => [// | le_il_k]; rewrite -lezNgt in le_il_k.
have // : n < n.
  rewrite (ltr_le_trans (2 ^ (il + 1))) // (ler_trans (2 ^ (k + 1))) //.
  by rewrite -(ge2_exp_le_equiv 2) // 1:addz_ge0 //
             1:addz_ge0 // ler_add2r.
qed.

lemma divpow2_start (n : int) :
  divpow2 n 0 = n.
proof.
by rewrite /divpow2 expr0 divz1.
qed.

lemma divpow2_next_new_ub (m n k l : int) :
  1 <= n => 0 <= k => divpow2 n k <= m => m %/ 2 <= l =>
  divpow2 n (k + 1) <= l.
proof.
rewrite /divpow2 => ge1_n ge0_k dp2_n_k_le_m m_div2_le_l.
rewrite exprS // mulrC.
rewrite div_2n_eq_div_n_div_2 1:(ler_trans 1) // 1:expr_gt0 //.
by rewrite (ler_trans (m %/ 2)) 1:leq_div2r.
qed.

lemma divpow2_next_same_ub (n k m : int) :
  1 <= n => 0 <= k => divpow2 n k <= m =>
  divpow2 n (k + 1) <= m.
proof.
move => ge1_n ge0_k dp2_n_k_le_m.
rewrite (divpow2_next_new_ub m) // leq_div //.
by rewrite (ler_trans (divpow2 n k)) // divpow2_ge0 1:(ler_trans 1).
qed.

lemma divpow2_next_new_lb (n k l m : int) :
  1 <= n => 0 <= k => m <= divpow2 n k => l <= m %/ 2 =>
  l <= divpow2 n (k + 1).
proof.
rewrite /divpow2 => ge1_n ge0_k m_le_dp2_n_k l_le_m_div2.
rewrite exprS // mulrC.
rewrite div_2n_eq_div_n_div_2 1:(ler_trans 1) // 1:expr_gt0 //.
by rewrite (ler_trans (m %/ 2)) // leq_div2r.
qed.

lemma divpow2_next_when_eq1 (n k : int) :
  1 <= n => 0 <= k => divpow2 n k = 1 =>
  divpow2 n (k + 1) = 0.
proof.
move => ge1_n ge0_k eq1_dp2_n_k.
by rewrite divpow2_le1_next_eq0 // eq1_dp2_n_k.
qed.

(* integer division rounding up by power of two *)

op divpow2up (n k : int) : int =
  n %%/ (2 ^ k).

lemma le_divpow2_divpow2up (n k : int) :
  divpow2 n k <= divpow2up n k.
proof.
rewrite /divpow2 /divpow2up /(%%/).
case (2 ^ k %| n) => [two2k_dvdz_n // | not_two2k_dvdz_n].
by rewrite ler_paddr.
qed.

lemma divpow2up_ge1 (n k : int) :
  1 <= n => 0 <= k => 1 <= divpow2up n k.
proof.
move => ge1_n ge0_k; rewrite /divpow2up /(%%/).
case (2 ^ k %| n) => [two2k_dvdz_n /= | not_two2k_dvdz_n].
rewrite lez_divRL 1:expr_gt0 //=.
rewrite dvdz_eq in two2k_dvdz_n.
case (n %/ 2 ^ k = 0) => [eq0_n_div_two2k | ne0_n_div_two2k].
move : two2k_dvdz_n.
rewrite eq0_n_div_two2k /= => eq0_n.
move : ge1_n.
by rewrite -eq0_n.
have ge1_n_div_two2k : 0 < n %/ 2 ^ k.
  by rewrite ltz_def ne0_n_div_two2k /= 1:int_div_ge0 1:(ler_trans 1) //
             exprn_ege1.
rewrite ltzE /= in ge1_n_div_two2k.
rewrite -two2k_dvdz_n ler_pmull 1:expr_gt0 //.
by rewrite ler_paddl // int_div_ge0 1:(ler_trans 1) // exprn_ege1.
qed.

lemma divpow2up_next_lt (n k : int) :
  1 <= n => 0 <= k => 2 <= divpow2up n k =>
  divpow2up n (k + 1) < divpow2up n k.
proof.
rewrite /divpow2up => ge1_n ge0_k ge2_dp2u_n_k.
rewrite exprS // mulrC divru_2n_eq_divru_n_divru_2 1:(ler_trans 1)
        // 1:expr_gt0 //.
by rewrite int_div2_up_le_self_if_ge2.
qed.

lemma divpow2up_eq1_int_log_up_le (n k : int) :
  1 <= n => 0 <= k => divpow2up n k = 1 =>
  int_log_up 2 n <= k.
proof.
rewrite /divpow2up /(%%/) /int_log_up => ge1_n ge0_k.
case (2 ^ k %| n) =>
  [two2k_dvdz_n /= eq1_n_div_two2k |
   not_two2k_dvdz_n eq1_n_div_two2k_plus1].
have <- := divpow2_eq1_int_log n k _ _ _ => //.
  have -> // : 2 ^ k = n.
have n_eq := divz_eq n (2 ^ k).
rewrite /(%|) in two2k_dvdz_n.
rewrite two2k_dvdz_n /= in n_eq.
rewrite eq1_n_div_two2k /= in n_eq.
by rewrite n_eq.
rewrite eq_sym -subr_eq /= eq_sym in eq1_n_div_two2k_plus1.
by rewrite divpow2_eq0_int_log_up_le.
qed.

lemma divpow2up_ge2_lt_int_log_up (n k : int) :
  1 <= n => 0 <= k => 2 <= divpow2up n k =>
  k < int_log_up 2 n.
proof.
rewrite /divpow2up => ge1_n ge0_k dp2u_n_k.
have lt_two2k_n : 2 ^ k < n.
  move : dp2u_n_k; rewrite /(%%/).
  case (2 ^ k %| n) =>
    /= [_ | not_two2k_dvdz_n ge2_ndivtwo2k_plus1].
  rewrite lez_divRL 1:expr_gt0 // mul2l => le_two2k_plus_more_n.
  by rewrite (ltr_le_trans (2 ^ k + 2 ^ k)) // ltr_spaddr 1:expr_gt0.
  rewrite -ler_subl_addr /= lez_divRL 1:expr_gt0 // 1:mul1r
    in ge2_ndivtwo2k_plus1.
  rewrite ltz_def ge2_ndivtwo2k_plus1 /=.
  case (n = 2 ^ k) => [eq_n_two2k | //].
  move : not_two2k_dvdz_n; by rewrite eq_n_two2k dvdzz.
have ge2_n : 2 <= n.
  rewrite ltzE in lt_two2k_n.
  rewrite (ler_trans (2 ^ k + 1)) //.
  have {1}-> : 2 = 1 + 1 by trivial.
  by rewrite lez_add2r exprn_ege1.
have [[_ eq1_n] | [#]] := int_log_upP 2 n _ _ => //.
move : ge2_n; by rewrite eq1_n.
pose ilu := int_log_up 2 n.
move => ge1_ilu lt_two2ilu_min1_n le_n_ilu.
case (k < ilu) => [// | le_ilu_k]; rewrite -lezNgt in le_ilu_k.
have // : n < n.
  rewrite (ler_lt_trans (2 ^ ilu)) // (ler_lt_trans (2 ^ k)) //.
  by rewrite -(ge2_exp_le_equiv 2) // int_log_up_ge0.
qed.

lemma divpow2up_start (n k l m : int) :
  divpow2up n 0 = n.
proof.
by rewrite /divpow2up /(%%/) expr0 (dvd1z n).
qed.

lemma divpow2up_next_new_ub (m n k l : int) :
  1 <= n => 0 <= k => divpow2up n k <= m => m %%/ 2 <= l =>
  divpow2up n (k + 1) <= l.
proof.
rewrite /divpow2up => ge1_n ge0_k dp2u_n_k_le_m m_div2u_le_l.
rewrite exprS // mulrC.
rewrite divru_2n_eq_divru_n_divru_2 1:(ler_trans 1) // 1:expr_gt0 //.
by rewrite (ler_trans (m %%/ 2)) 1:le_div_rnd_up.
qed.

lemma divpow2up_next_same_ub (n k m : int) :
  1 <= n => 0 <= k => divpow2up n k <= m =>
  divpow2up n (k + 1) <= m.
proof.
move => ge1_n ge0_k dp2u_n_k_le_m.
rewrite (divpow2up_next_new_ub m) // int_div2_up_le_self.
by rewrite (ler_trans 1) // (ler_trans (divpow2up n k)) 1:divpow2up_ge1.
qed.

lemma divpow2up_next_new_lb (m n k l : int) :
  1 <= n => 0 <= k => m <= divpow2up n k => l <= m %%/ 2 =>
  l <= divpow2up n (k + 1).
proof.
rewrite /divpow2up => ge1_n ge0_k m_le_dp2u_n_k l_le_m_div2u.
rewrite exprS // mulrC.
rewrite divru_2n_eq_divru_n_divru_2 1:(ler_trans 1) // 1:expr_gt0 //.
by rewrite (ler_trans (m %%/ 2)) // le_div_rnd_up.
qed.
