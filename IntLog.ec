(* Working with Bounds Involving Integer Logarithms *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2021-2022 - Boston University
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

prover [""].  (* no use of SMT provers *)

require import AllCore StdOrder IntDiv RealExp FloorCeil.
import IntOrder.

(* multiplication by 2 *)

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

(* lemmas about exponentiation and <=/< *)

lemma ge2_exp_le_equiv (d n m : int) :
  2 <= d => 0 <= n => 0 <= m =>
  n <= m <=> d ^ n <= d ^ m.
proof.
move => ge2_d ge0_n ge0_m.
split => [le_n_m | le_d2n_d2m].
by rewrite ler_weexpn2l 1:(ler_trans 2).
case (n <= m) => [// | lt_m_n]; rewrite -ltrNge in lt_m_n.
have le_d2m_d2n : d ^ m <= d ^ n.
  by rewrite ler_weexpn2l // 1:(ler_trans 2) // 1:ge0_m /= ltzW.
have eq_d2m_d2n : d ^ m = d ^ n by apply ler_asym.
have eq_m_n : m = n.
  rewrite (ieexprIn d _ _ m n) 1:(ltr_le_trans 1) // 1:(ler_trans 2) //.
  by rewrite gtr_eqF 1:(ltr_le_trans 2).
move : lt_m_n; by rewrite eq_m_n.
qed.

lemma ge2_exp_lt_equiv (d n m : int) :
  2 <= d => 0 <= n => 0 <= m =>
  n < m <=> d ^ n < d ^ m.
proof.
move => ge2_d ge0_n ge0_m.
split => [lt_n_m | lt_d2n_d2m].
rewrite ltz_def -ge2_exp_le_equiv // ltzW //=.
case (d ^ m = d ^ n) => [eq_d2m_d2n | //].
have eq_m_n : m = n.
  rewrite (ieexprIn d _ _ m n) 1:(ltr_le_trans 1) // 1:(ler_trans 2) //.
  by rewrite gtr_eqF 1:(ltr_le_trans 2).
move : lt_n_m; by rewrite eq_m_n.
rewrite ltz_def (ge2_exp_le_equiv d) // ltzW //=.
case (m = n) => [eq_m_n | //].
move : lt_d2n_d2m; by rewrite eq_m_n.
qed.

(* lemmas about being even and odd *)

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

lemma even_iff_eq (m : int) :
  2 %| m <=> m = (m %/ 2) * 2.
proof. by rewrite dvdz_eq eq_sym. qed.

lemma odd_iff_eq (m : int) :
  ! 2 %| m <=> m = (m %/ 2) * 2 + 1.
proof.
split => [odd_m | ->].
rewrite {1}(divz_eq m 2).
congr.
by rewrite -ne0_mod2.
by rewrite -even_iff_plus1_odd dvdz_mull.
qed.

(* lemmas about integer division, both rounding down (%/) and
   (new) rounding up (%%/) *)

lemma div_succ_plus1 (b m : int) :
  1 <= b => b %| (m + 1) => (m + 1) %/ b = m %/ b + 1.
proof.
move => ge1_b b_dvdz_m_plus1.
have ne0_b : b <> 0 by rewrite ltr0_neq0 1:(ltr_le_trans 1).
rewrite (addrC (m %/ b)) -divzMDr //=.
have -> : (m + b = (m + 1) + (b - 1)) by algebra.
rewrite (divzDl (m + 1)) // (divz_small (b - 1)) //.
rewrite ler_subr_addr /= ge1_b /=.
by rewrite gtr0_norm ltzE.
qed.

lemma div_succ_eq (b m : int) :
  1 <= b => ! b %| (m + 1) => (m + 1) %/ b = m %/ b.
proof.
move => ge1_b not_b_dvdz_m_plus1.
have ne0_b : b <> 0 by rewrite ltr0_neq0 1:(ltr_le_trans 1).
have -> : m = (m + 1) %/ b * b + (m + 1) %% b - 1.
  have m_plus1_eq := divz_eq (m + 1) b.
  by rewrite eq_sym subr_eq eq_sym.
rewrite /= divzDl 1:dvdz_mull 1:dvdzz.
rewrite -addrA (divzDl _ ((m + 1) %% b - 1)) 1:dvdz_mull 1:dvdzz.
congr.
rewrite divz_small 1:modz_ge0 //= 1:ltz_mod //.
rewrite divz_small // ler_subr_addr -ltzE lt0r.
rewrite -dvdzE not_b_dvdz_m_plus1 /= modz_ge0 //=.
rewrite (ltr_trans ((m + 1) %% b)).
by rewrite ltr_subl_addr 1:ltzS.
by rewrite ltz_mod.
qed.

lemma int_div_ge0 (m d : int) :
  0 <= m => 1 <= d => 0 <= m %/ d.
proof.
move => ge0_m ge1_d.
by rewrite divz_ge0 1:(ltr_le_trans 1).
qed.

lemma int_div_lt_b_implies_eq0 (b m : int) :
  1 <= b => 0 <= m < b => m %/ b = 0.
proof.
move => ge1_b [ge0_m lt_m_b].
by rewrite -divz_eq0 // ltzE.
qed.

lemma int_div2_0or1_implies_eq0 (m : int) :
  0 <= m <= 1 => m %/ 2 = 0.
proof.
move => [ge0_m le1_m].
rewrite int_div_lt_b_implies_eq0 // ge0_m /=.
have -> : 2 = 1 + 1 by trivial.
by rewrite ltzS.
qed.

lemma int_div_ge_b_implies_ge1 (b m : int) :
  1 <= b => b <= m => 1 <= m %/ b.
proof.
move => ge1_b le_b_m.
have ne0_b : b <> 0 by rewrite ltr0_neq0 1:(ltr_le_trans 1).
have [p [ge0_p ->]] : exists p, 0 <= p /\ m = b + p.
  exists (m - b); split; [by rewrite ler_subr_addr | algebra].
by rewrite divzDl 1:dvdzz divzz ne0_b b2i1 ler_paddr 1:int_div_ge0.
qed.

lemma int_div2_ge2_implies_ge1 (m : int) :
  2 <= m => 1 <= m %/ 2.
proof.
move => ge2_m.
by rewrite int_div_ge_b_implies_ge1.
qed.

lemma int_div_lt_self_if_ge1 (b m : int) :
  2 <= b => 1 <= m => m %/ b < m.
proof.
move => ge2_b ge1_m.
have gt0_b : 0 < b by rewrite (ltr_le_trans 2).
have gt1_b : 1 < b by rewrite (ltr_le_trans 2).
have gt0_m : 0 < m by rewrite ltzE.
by rewrite (ltz_divLR m m b) // ltr_pmulr.
qed.

lemma int_div2_lt_self_if_ge1 (m : int) :
  1 <= m => m %/ 2 < m.
proof.
move => ge1_m.
by rewrite int_div_lt_self_if_ge1.
qed.

lemma div_nb_eq_div_n_div_b (b m n : int) :
  1 <= b => 0 <= m => 0 < n =>
  m %/ (n * b) = m %/ n %/ b.
proof.
move => ge1_b ge0_m gt0_n.
have gt0_b : 0 < b by rewrite (ltr_le_trans 1).
have ne0_n_tim_b : n * b <> 0 by rewrite gtr_eqF 1:pmulr_lgt0.
rewrite {2}(divz_eq m (n * b)).
have -> : m %/ (n * b) * (n * b) = m %/ (n * b) * b * n.
  by rewrite -mulrA (mulrC b).
rewrite divzMDl 1:gtr_eqF // 1:divzMDl // 1:ltr0_neq0 //.
have -> // : m %% (n * b) %/ n %/ b = 0.
  rewrite divz_small //.
  split => [| _].
  by rewrite divz_ge0 // modz_ge0 ne0_n_tim_b.
  rewrite ltz_divLR // ger0_norm // 1:ltzW // (mulrC b).
  rewrite -{2}(ger0_norm (n * b)) 1:mulr_ge0 1:ltzW // 1:ltzW //.
  by rewrite ltz_mod ne0_n_tim_b.
qed.

lemma div_2n_eq_div_n_div_2 (m n : int) :
  0 <= m => 0 < n =>
  m %/ (n * 2) = m %/ n %/ 2.
proof.
move => ge0_m gt0_n.
by rewrite div_nb_eq_div_n_div_b.
qed.

(* like m %/ d, but add 1 if non-zero remainder: *)

op nosmt (%%/) (m d : int) : int =
  m %/ d + ((d %| m) ? 0 : 1).

lemma int_div_up_dvdz_b (b n : int) :
  b %| n => n %%/ b = n %/ b.
proof.
move => b_dvdz_n.
by rewrite /(%%/) b_dvdz_n.
qed.

lemma int_div_up2_even (n : int) :
  2 %| n => n %%/ 2 = n %/2.
proof.
move => even_n.
by rewrite int_div_up_dvdz_b.
qed.

lemma int_div_up2_odd (n : int) :
  ! 2 %| n => n %%/ 2 = (n + 1) %/ 2.
proof.
move => odd_n.
by rewrite /(%%/) odd_n /= div_succ_plus1 // -odd_iff_plus1_even.
qed.

lemma int_div2_le_int_div2_up (m d : int) :
  m %/ d <= m %%/ d.
proof.
rewrite /(%%/).
case (d %| m) => [d_dvdz_m // | not_d_dvdz_m].
by rewrite ler_paddr.
qed.

lemma div2_plus_div2up_eq (n : int) :
  n = n %/ 2 + n %%/ 2.
proof.
rewrite /(%%/).
case (2 %| n) => /= [even_n | odd_n].
by rewrite -mul2r divzK.
by rewrite addrA -mul2r -odd_iff_eq.
qed.

lemma int_div_up_eq0_implies_eq0 (b m : int) :
  1 <= b => 0 %%/ b = 0.
proof. trivial. qed.

lemma int_div2_up_eq0_implies_eq0 (m : int) :
  0 %%/ 2 = 0.
proof. trivial. qed.

lemma int_div_up_b_ge1_ge_b_implies_ge1 (b m : int) :
  1 <= b => b <= m => 1 <= m %%/ b.
proof.
move => ge1_b le_b_m; rewrite /(%%/).
case (b %| m) => /=.
by rewrite int_div_ge_b_implies_ge1.
by rewrite lez_addr int_div_ge0 1:(ler_trans b) 1:(ler_trans 1).
qed.

lemma int_div_up_ge1_implies_ge1 (b m : int) :
  2 <= b => 1 <= m => 1 <= m %%/ b.
proof.
move => ge2_b ge1_m; rewrite /(%%/).
case (b %| m) => [b_dvdz_m /= | not_b_dvdz_m].
rewrite int_div_ge_b_implies_ge1 1:(ler_trans 2) //.
case (b <= m) => [// | lt_m_b].
rewrite lerNgt /= in lt_m_b.
have := divzK b m _ => //.
rewrite eq_sym => m_eq.
move : lt_m_b.
rewrite m_eq.
have {3}-> : b = 1 * b by trivial.
rewrite ltr_pmul2r 1:(ltr_le_trans 2) //.
have -> : 1 = 0 + 1 by trivial.
rewrite ltzS => le0_m_div_b.
have eq0_m_div_b : m %/ b = 0.
  by rewrite (ler_anti (m %/ b) 0) 1:le0_m_div_b /= 1:divz_ge0
             1:(ltr_le_trans 2) // (ler_trans 1).
move : m_eq.
rewrite eq0_m_div_b.
move => m_eq.
rewrite /= in m_eq.
have // : 1 <= 0 by rewrite (ler_trans m) // m_eq.
by rewrite ler_paddl 1:int_div_ge0 1:(ler_trans 1) // (ler_trans 2).
qed.

lemma int_div2_up_ge1_implies_ge1 (m : int) :
  1 <= m => 1 <= m %%/ 2.
proof.
move => ge1_m.
by rewrite int_div_up_ge1_implies_ge1.
qed.

lemma int_div_up_le_self (b m : int) :
  2 <= b => 0 <= m => m %%/ b <= m.
proof.
move => ge2_b ge0_m; rewrite /(%%/).
case (b %| m) => [b_dvdz_m /= | not_b_dvdz_m].
by rewrite leq_div // (ler_trans 2).
rewrite -ltzE ltz_divLR 1:(ltr_le_trans 2) //.
rewrite ltr_pmulr.
rewrite ltz_def ge0_m /=.
move : not_b_dvdz_m.
case (m = 0) => [-> contrad | //].
have // : b %| 0 by rewrite (dvdz0 b).
by rewrite (ltr_le_trans 2).
qed.

lemma int_div2_up_le_self (m : int) :
  0 <= m => m %%/ 2 <= m.
proof.
move => ge0_m.
by rewrite int_div_up_le_self.
qed.

lemma int_div_up_lt_self_if_ge_b (b m : int) :
  2 <= b => b <= m => m %%/ b < m.
proof.
move => ge2_b le_b_m; rewrite /(%%/).
case (b %| m) => [b_dvdz_m /= | not_b_dvdz_m].
by rewrite int_div_lt_self_if_ge1 // (ler_trans 2) // (ler_trans b).
have m_eq := divz_eq m b.
rewrite -ltr_subr_addr ltz_divLR 1:(ltr_le_trans 2) //.
have -> : (m - 1) * b = m * b - b by algebra.
rewrite ltr_subr_addr.
move : not_b_dvdz_m.
case (m = b) => [-> | ne_m_b _].
by rewrite dvdzz.
have lt_b_m : b < m by rewrite ltz_def ne_m_b.
rewrite (ltr_le_trans (m + m)) 1:ltz_add2l //.
by rewrite -mul2r ler_wpmul2l 1:(ler_trans b) 1:(ler_trans 2).
qed.

lemma int_div2_up_lt_self_if_ge2 (m : int) :
  2 <= m => m %%/ 2 < m.
proof.
move => ge2_m.
by rewrite int_div_up_lt_self_if_ge_b.
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

lemma divru_nb_eq_divru_n_divru_b (b m n : int) :
  1 <= b => 0 <= m => 0 < n =>
  m %%/ (n * b) = m %%/ n %%/ b.
proof.
move => ge1_b ge0_m gt0_n; rewrite /(%%/).
case ((n * b) %| m) => [nb_dvdz_m | not_nb_dvdz_m].
have m_nb_eq : m = m %/ (n * b) * (n * b).
  have eq_m_nb := divz_eq m (n * b).
  rewrite dvdzE in nb_dvdz_m.
  by rewrite nb_dvdz_m /= in eq_m_nb.
have -> /= : n %| m.
  rewrite m_nb_eq {2}(mulrC n) mulrA dvdz_mull dvdzz.
rewrite div_nb_eq_div_n_div_b //.
have -> // : b %| m %/ n.
  by rewrite m_nb_eq {2}(mulrC n) mulrA mulrC mulKz 1:gtr_eqF //
             dvdzE modzMl.
rewrite div_nb_eq_div_n_div_b //.
case (n %| m) => [n_dvdz_m /= | not_n_dvdz_m].
case (b %| m %/ n) => [b_dvdz_m_div_n | //].
have // : n * b %| m by rewrite dvdz_comp // (ltr_le_trans 1).
case (b %| (m %/ n + 1)) =>
  [b_dvdz_m_div_n_plus1 /= | not_b_dvdz_m_div_n_plus1].
by rewrite div_succ_plus1.
by rewrite div_succ_eq.
qed.

lemma divru_2n_eq_divru_n_divru_2 (m n : int) :
  0 <= m => 0 < n => m %%/ (n * 2) = m %%/ n %%/ 2.
proof.
move => ge0_m gt0_n.
by rewrite divru_nb_eq_divru_n_divru_b.
qed.

lemma div2_sum_le_bigger_or_eq (m n : int) :
  m <= n => (n + m) %/ 2 <= n.
proof.
move => ge_m_n.
have -> : n = (n - m) + m by algebra.
rewrite -{1}addrA -mul2r divzMDr //.
have -> : n - m + m = m + n - m by algebra.
by rewrite -addrA lez_add2l // leq_div 1:subr_ge0.
qed.

lemma div2_sum_lt_bigger (m n : int) :
  m < n => (n + m) %/ 2 < n.
proof.
move => lt_m_n.
have -> : n = (n - m) + m by algebra.
rewrite -{1}addrA -mul2r divzMDr //.
have -> : n - m + m = m + n - m by algebra.
rewrite -addrA ltr_add2l.
rewrite int_div2_lt_self_if_ge1.
rewrite ltzE -ler_subr_addl // in lt_m_n.
qed.

lemma divru2_sum_le_bigger_or_eq (m n : int) :
  m <= n => (n + m) %%/ 2 <= n.
proof.
move => ge_m_n.
case (m = n) => [-> | ne_m_n].
by rewrite -mul2r int_div_up2_even 1:dvdz_mull // mulzK.
have lt_m_n : m < n by rewrite ltr_def eq_sym.
rewrite /(%%/).
case (2 %| (n + m)) => [even_n_plus_m | odd_n_plus_m] /=.
by rewrite div2_sum_le_bigger_or_eq.
by rewrite -ltzE div2_sum_lt_bigger.
qed.

(* connections of %/ and %%/ with / and floor/ceil *)

lemma int_div_pos_floor (n b : int) :
  1 <= b => n %/ b = floor (n%r / b%r).
proof.
move => ge1_b; rewrite eq_sym.
have gt0_b : 0 < b by rewrite ltzE.
have ne0_d : b <> 0 by rewrite IntOrder.gtr_eqF.
rewrite (divz_eq n b); pose m := n %/ b; pose l := n %% b.
have ge0_l : 0 <= l by rewrite modz_ge0.
have lt_l_b : l < b by rewrite ltz_pmod.
rewrite divzMDl // pdiv_small //=.
rewrite fromintD fromintM.
rewrite RField.mulrDl -RField.mulrA RField.mulfV 1:eq_fromint //=.
have ge0_l_div_b_r : 0%r <= l%r / b%r.
  by rewrite RealOrder.divr_ge0 le_fromint // ltzW.
have lt1_l_div_b_r : l%r / b%r < 1%r.
  by rewrite RealOrder.ltr_pdivr_mulr 1:lt_fromint //= lt_fromint.
apply floorE; split => [| _].
by rewrite RealOrder.ler_addl.
by rewrite fromintD RealOrder.ltr_add2l.
qed.

lemma int_div_up_pos_ceil (n b : int) :
  1 <= b => n %%/ b = ceil (n%r / b%r).
proof.
move => ge1_b; rewrite /(%%/) eq_sym.
have gt0_b : 0 < b by rewrite ltzE.
have ne0_b : b <> 0 by rewrite IntOrder.gtr_eqF.
rewrite (divz_eq n b); pose m := n %/ b; pose l := n %% b.
have ge0_l : 0 <= l by rewrite modz_ge0.
have lt_l_b : l < b by rewrite ltz_pmod.
case (l = 0) => [-> /= | ne0_l].
rewrite dvdz_mull 1:dvdzz /= mulzK //.
by rewrite fromintM -RField.mulrA RField.mulfV 1:eq_fromint //= from_int_ceil.
have gt0_l : 0 < l by rewrite ltz_def.
have ge0_l_div_b_r : 0%r <= l%r / b%r.
  by rewrite RealOrder.divr_ge0 le_fromint // ltzW.
have le1_l_div_b_r : l%r / b%r <= 1%r.
  by rewrite RealOrder.ler_pdivr_mulr 1:lt_fromint //= le_fromint ltzW.
rewrite divzMDl // pdiv_small //=.
rewrite dvdzE modzMDl pmod_small // ne0_l /=.
rewrite fromintD fromintM.
rewrite RField.mulrDl -RField.mulrA RField.mulfV 1:eq_fromint //=.
apply ceilE; split => [| _].
by rewrite -addzA /= RealOrder.ltr_addl RealOrder.divr_gt0 lt_fromint.
by rewrite fromintD RealOrder.ler_add2l.
qed.

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

lemma int_log_ub_lt (b n : int) :
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

lemma int_log_lt_b_eq0 (b n : int) :
  2 <= b => 1 <= n < b => int_log b n = 0.
proof.
move => ge2_b [ge1_n lt_n_b].
by rewrite eq_sym (int_logPuniq b n) // 1:expr0 /= 1:expr1 lt_n_b.
qed.

lemma int_log1_eq0 (b : int) :
  2 <= b => int_log b 1 = 0.
proof.
move => ge2_b.
by rewrite int_log_lt_b_eq0 //= ltzE.
qed.

lemma int_log_ge1_when_ge_b (b n : int) :
  2 <= b => b <= n => 1 <= int_log b n.
proof.
move => ge2_b le_b_n.
have ge1_n : 1 <= n by rewrite (ler_trans b) // (ler_trans 2).
have -> : 1 = 1 + 0 by trivial.
rewrite lez_add1r ltz_def int_log_ge0 //=.
case (int_log b n = 0) => [eq0_il_n | //].
have lt_n_b2_1 := int_log_ub_lt b n _ _ => //.
rewrite eq0_il_n /= expr1 in lt_n_b2_1.
have // : b < b by rewrite (ler_lt_trans n).
qed.

lemma int_log_le (b n m : int) :
  2 <= b => 1 <= n <= m =>
  int_log b n <= int_log b m.
proof.
move => ge2_b [ge1_n le_n_m].
have ge1_m : 1 <= m by rewrite (ler_trans n).
case (int_log b n <= int_log b m) => [// | il_m_plus1_le_il_n].
rewrite lerNgt /= ltzE in il_m_plus1_le_il_n.
have [#] _ b2il_n_le_n _ := int_logP b n _ _ => //.
have [#] _ _ m_lt_b2il_m_plus1 := int_logP b m _ _ => //.
have lt_m_n : m < n.
  rewrite (ltr_le_trans (b ^ (int_log b m + 1))) //.
  rewrite (ler_trans (b ^ (int_log b n))) //.
  rewrite ler_weexpn2l 1:(ler_trans 2) // il_m_plus1_le_il_n /=.
  by rewrite addz_ge0 1:int_log_ge0.
have // : n < n by rewrite (ler_lt_trans m).
qed.

lemma int_log_pow_b (b i : int) :
  2 <= b => 0 <= i =>
  int_log b (b ^ i) = i.
proof.
move => ge2_b ge0_i.
have ge1_b2i: 1 <= b ^ i by rewrite exprn_ege1 // (ler_trans 2).
have [#] ge0_il_b2i b2ilb2i_le_b2i b2i_lt_b2ilb2i_plus1
     := int_logP b (b ^ i) _ _ => //.
rewrite (ler_anti (int_log b (b ^ i)) i) //.
split => [| _].
rewrite (ge2_exp_le_equiv b (int_log b (b ^ i)) i) //.
move : b2i_lt_b2ilb2i_plus1.
rewrite -(ge2_exp_lt_equiv b i (int_log b (b ^ i) + 1)) //.
by rewrite addz_ge0 1:int_log_ge0.
by rewrite ltzS.
qed.

lemma int_log_distr_mul (b n m : int) :
  2 <= b => 1 <= n => 1 <= m =>
  int_log b n + int_log b m <=
  int_log b (n * m) <=
  int_log b n + int_log b m + 1.
proof.
move => ge2_b ge1_n ge1_m.
have ge0_b : 0 <= b by rewrite (ler_trans 2).
have ge0_n : 0 <= n by rewrite (ler_trans 1).
have ge0_m : 0 <= m by rewrite (ler_trans 1).
have [ge0_il_b_n [b2il_b_n_le_n n_lt_b2_il_b_n_plus1]]
     := int_logP b n _ _ => //.
have [ge0_il_b_m [b2il_b_m_le_m m_lt_b2_il_b_m_plus1]]
     := int_logP b m _ _ => //.
have nm_b2_lb_le : b ^ (int_log b n + int_log b m) <= n * m.
  rewrite exprD_nneg // ler_pmul // expr_ge0 ge0_b.
have nm_b2_ub_lt : n * m < b ^ (int_log b n + int_log b m + 2).
  have -> :
    (int_log b n + int_log b m + 2) =
    (int_log b n + 1) + (int_log b m + 1) by algebra.
  rewrite exprD_nneg 1:addr_ge0 // 1:addr_ge0 // ltr_pmul //.
case (n * m < b ^ (int_log b n + int_log b m + 1)) =>
  [nm_lt_b2_il_b_n_plus_il_b_m_plus1 | b2_il_b_n_plus_il_b_m_plus1_le_nm].
have il_b_nm_eq_il_b_n_plus_il_b_m :
  int_log b (n * m) = int_log b n + int_log b m.
  by rewrite (int_logPuniq b (n * m) (int_log b n + int_log b m)) //
             1:addr_ge0.
split => [| _].
by rewrite il_b_nm_eq_il_b_n_plus_il_b_m.
by rewrite -il_b_nm_eq_il_b_n_plus_il_b_m ler_addl.
rewrite -lerNgt in b2_il_b_n_plus_il_b_m_plus1_le_nm.
have il_b_nm_eq_il_b_n_plus_il_b_m_plus1 :
  int_log b (n * m) = int_log b n + int_log b m + 1.
  by rewrite (int_logPuniq b (n * m) (int_log b n + int_log b m + 1)) //
             addr_ge0 1:addr_ge0.
split => [| _].
by rewrite il_b_nm_eq_il_b_n_plus_il_b_m_plus1 ler_addl.
by rewrite -il_b_nm_eq_il_b_n_plus_il_b_m_plus1.
qed.

lemma int_log_distr_mul_lb (b n m : int) :
  2 <= b => 1 <= n => 1 <= m =>
  int_log b n + int_log b m <= int_log b (n * m).
proof.
move => ge2_b ge1_n ge1_m.
have := int_log_distr_mul b n m _ _ _ => //.
qed.

lemma int_log_distr_mul_ub (b n m : int) :
  2 <= b => 1 <= n => 1 <= m =>
  int_log b (n * m) <= int_log b n + int_log b m + 1.
proof.
move => ge2_b ge1_n ge1_m.
have := int_log_distr_mul b n m _ _ _ => //.
qed.

lemma int_log_div (b n : int) :
  2 <= b => b <= n =>
  int_log b (n %/ b) = int_log b n - 1.
proof.
move => ge2_b le_b_n.
have ge0_b : 0 <= b by rewrite (ler_trans 2).
have ge1_b : 1 <= b by rewrite (ler_trans 2).
have ge1_n : 1 <= n by rewrite (ler_trans b) // (ler_trans 2).
have ge1_il_n : 1 <= int_log b n by rewrite int_log_ge1_when_ge_b.
rewrite (int_logPuniq b (n %/ b) (int_log b n - 1)) //=.
by rewrite ler_subr_addr.
have [#] _ := int_logP b n _ _ => //.
have -> : int_log b n = (int_log b n - 1) + 1 by algebra.
pose p := int_log b n - 1.
have ge0_p : 0 <= p by rewrite /p ler_subr_addr.
have ge0_p_plus1 : 0 <= p + 1 by rewrite addz_ge0.
rewrite {1}(exprS _ p) // (mulrC _ (b ^ p)).
rewrite {1}(exprS _ (p + 1)) // 1:(mulrC _ (b ^ (p + 1))).
move => b2p_tim_b_le_n n_lt_b2p_plus1_tim_b /=.
split => [| _].
have -> : b ^ p = b ^ p * b %/ b by rewrite mulzK // lt0r_neq0 1:ltzE.
by rewrite leq_div2r.
by rewrite ltz_divLR 1:ltzE.
qed.

(* integer logarithm rounding up (should not be applied when b <= 1 or
   n <= 0) *)

op int_log_up (b n : int) : int =
  int_log b n + ((b ^ int_log b n = n) ? 0 : 1).

lemma int_log_int_log_up_le (b n : int) :
  int_log b n <= int_log_up b n.
proof.
rewrite /int_log_up.
case (b ^ int_log b n = n) => [// | _].
by rewrite ler_paddr.
qed.

lemma int_log_int_log_up_eq_iff (b n : int) :
  2 <= b => 1 <= n =>
  int_log b n = int_log_up b n <=> b ^ int_log b n = n.
proof.
move => ge2_b ge1_n.
rewrite /int_log_up.
case (b ^ int_log b n = n) => [// | _ /=].
case (int_log b n = int_log b n + 1) => [| //].
by rewrite addrC -subr_eq.
qed.

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
have [[->] | [ge1_ilu _]] := int_log_upP b n _ _ => //.
by rewrite (ler_trans 1).
qed.

lemma int_log_up_zero_iff (b n : int) :
  2 <= b => 1 <= n =>
  int_log_up b n = 0 <=> n = 1.
proof.
move => ge2_b ge1_n.
have [// | [#] ge1_il lt_b2ilu_min1_n _] := int_log_upP b n _ _ => //.
split => [eq0_ilu | eq1_n].
have // : 1 <= 0 by rewrite (ler_trans (int_log_up b n)) // eq0_ilu.
have : b ^ (int_log_up b n - 1) = 0.
  rewrite eqr_le.
  split => [| _].
  by rewrite -ltzS /= -{2}eq1_n.
  rewrite expr_ge0 (ler_trans 2) //.
rewrite expf_eq0 => [[_ eq0_b]].
have // : 2 <= 0 by rewrite (ler_trans b) // eq0_b.
qed.

lemma int_log_up_ge2_implies_ge1 (b n : int) :
  2 <= b => 2 <= n => 1 <= int_log_up b n.
proof.
move => ge2_b ge2_n.
have [[_ eq1_n] |] := int_log_upP b n _ _ => //.
  by rewrite (ler_trans 2).
have // : 2 <= 1 by rewrite -eq1_n.
qed.

lemma int_log_up_ge2_lb_lt (b n : int) :
  2 <= b => 2 <= n => b ^ (int_log_up b n - 1) < n.
proof.
move => ge2_b ge2_n.
have [[_ eq1_n] |] := int_log_upP b n _ _ => //.
  by rewrite (ler_trans 2).
have // : 2 <= 1 by rewrite -eq1_n.
qed.

lemma int_log_up_ge2_ub_le (b n : int) :
  2 <= b => 2 <= n => n <= b ^ (int_log_up b n).
proof.
move => ge2_b ge2_n.
have [[_ eq1_n] |] := int_log_upP b n _ _ => //.
  by rewrite (ler_trans 2).
have // : 2 <= 1 by rewrite -eq1_n.
qed.

lemma int_log_up_ge2_uniq (b n k1 k2 : int) :
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

lemma int_log_up_ge2_Puniq (b n l : int) :
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
by apply (int_log_up_ge2_uniq b n).
qed.

lemma int_log_up_le (b n m : int) :
  2 <= b => 1 <= n <= m =>
  int_log_up b n <= int_log_up b m.
proof.
move => ge2_b [ge1_n le_n_m].
have ge1_m : 1 <= m by rewrite (ler_trans n).
case (int_log_up b n <= int_log_up b m) => [// | ilu_m_plus1_le_ilu_n].
rewrite lerNgt /= ltzE in ilu_m_plus1_le_ilu_n.
have [[eq0_ilu_n _] | [#] _ b2ilu_n_min1_lt_n _] := int_log_upP b n _ _ => //.
move : ilu_m_plus1_le_ilu_n.
rewrite eq0_ilu_n => le0_ilu_m_plus1.
have // : 1 <= 0.
  by rewrite (ler_trans (int_log_up b m + 1)) // ler_addr int_log_up_ge0.
have [[eq0_ilu_m eq1_m] | [#] _ _ le_m_b2ilu_m] := int_log_upP b m _ _ => //.
have eq1_n : n = 1.
  move : le_n_m; rewrite eq1_m => le1_n.
  rewrite (ler_anti n 1) 1:le1_n //.
rewrite -(int_log_up_zero_iff b n) // in eq1_n.
have // : 1 <= 0.
  have -> : 1 = int_log_up b m + 1.
  by rewrite eq0_ilu_m.
  by rewrite (ler_trans (int_log_up b n)) // eq1_n.
have ilu_m_le_ilu_n_min1 : int_log_up b m <= int_log_up b n - 1.
  by rewrite -ler_subr_addr in ilu_m_plus1_le_ilu_n.
have lt_m_n : m < n.
  rewrite (ler_lt_trans (b ^ (int_log_up b m))) //.
  rewrite (ler_lt_trans (b ^ (int_log_up b n - 1))) //.
  rewrite -ge2_exp_le_equiv // 1:int_log_up_ge0 //.
  rewrite (ler_trans (int_log_up b m)) 1:int_log_up_ge0 //.
have // : n < n by rewrite (ler_lt_trans m).
qed.

lemma int_log_up_pow_b (b i : int) :
  2 <= b => 0 <= i =>
  int_log_up b (b ^ i) = i.
proof.
move => ge2_b ge0_i.
have ge1_b2i: 1 <= b ^ i by rewrite exprn_ege1 // (ler_trans 2).
have [[-> eq1_b2i ] | [#] ge1_ilu b2ilu_b2i_min1_lt_b2i b2i_le_b2_ilu_b2i]
     := int_log_upP b (b ^ i) _ _ => //.
rewrite (ler_anti 0 i) // 1:ge0_i /=.
case (i <= 0) => [// | gt0_i].
rewrite lerNgt /= in gt0_i.
have le_b_b2i : b <= b ^ i by rewrite ler_eexpr // (ler_trans 2).
rewrite eq1_b2i in le_b_b2i.
have // : 2 <= 1 by rewrite (ler_trans b).
rewrite (ler_anti (int_log_up b (b ^ i)) i) //.
split.
move : b2ilu_b2i_min1_lt_b2i.
by rewrite -(ge2_exp_lt_equiv b (int_log_up b (b ^ i) - 1) i) //
           1:ler_subr_addr // ltr_subl_addl addrC ltzS.
by rewrite (ge2_exp_le_equiv b i (int_log_up b (b ^ i))) // int_log_up_ge0.
qed.

lemma real_log_bounds (b n : int) :
  2 <= b => 1 <= n =>
  (int_log b n)%r <= log b%r n%r <= (int_log_up b n)%r.
proof.
move => ge2_b ge1_n.
have gt0_n : 0 < n by rewrite (ltr_le_trans 1).
have zr_lt_nr : 0%r < n%r by rewrite lt_fromint.
have ge0_b : 0 <= b by rewrite (ler_trans 2).
have zr_le_br : 0%r <= b%r by rewrite le_fromint.
have gt0_b : 0 < b by rewrite (ltr_le_trans 2).
have zr_lt_br : 0%r < b%r by rewrite lt_fromint.
have gt1_b : 1 < b by rewrite (ltr_le_trans 2).
have or_lt_br : 1%r < b%r by rewrite lt_fromint.
split => [| _].
have -> :
  (int_log b n)%r = log b%r (b %r ^ (int_log b n)%r).
  by rewrite logK // eq_fromint gtr_eqF.
rewrite log_mono // 1:rpow_gt0 // 1:rpow_nat // 1:int_log_ge0 //.
rewrite RField.fromintXn 1:int_log_ge0 // 1:le_fromint //.
by rewrite int_log_lb_le.
case (n = 1) => [-> | ne1_n].
have -> : int_log_up b 1 = 0 by rewrite int_log_up_zero_iff.
have -> : 1%r = b%r ^ 0 by rewrite RField.expr0.
rewrite -rpow_nat // logK // eq_fromint gtr_eqF //.
have ge2_n : 2 <= n.
  have -> : 2 = 1 + 1 by trivial.
  by rewrite -ltzE ltz_def.
have -> :
  (int_log_up b n)%r = log b%r (b %r ^ (int_log_up b n)%r).
  by rewrite logK // eq_fromint gtr_eqF.
rewrite log_mono // 1:rpow_gt0 // 1:rpow_nat // 1:int_log_up_ge0 //.
rewrite RField.fromintXn 1:int_log_up_ge0 // 1:le_fromint //.
by rewrite int_log_up_ge2_ub_le.
qed.

lemma real_log_ub_lt (b n : int) :
  2 <= b => 1 <= n => b ^ (int_log b n) <> n =>
  log b%r n%r < (int_log_up b n)%r.
proof.
move => ge2_b ge1_n b2il_bn_ne_n.
have [_] := real_log_bounds b n _ _ => //.
rewrite /int_log_up b2il_bn_ne_n /= => log_bn_le_il_bn_plus1.
rewrite RealOrder.ltr_def log_bn_le_il_bn_plus1 /=.
case ((int_log b n + 1)%r <> log b%r n%r) => [// | contrad].
rewrite /= in contrad.
have n_eq_b2_il_bn_plus1 : n = b ^ (int_log b n + 1).
  rewrite -eq_fromint -RField.fromintXn.
  rewrite addz_ge0 1:int_log_ge0 //.
  rewrite -rpow_nat 1:addz_ge0 1:int_log_ge0 //.
  rewrite le_fromint 1:(ler_trans 2) //.
  rewrite contrad rpowK //.
  rewrite lt_fromint (ltr_le_trans 2) //.
  rewrite eq_fromint gtr_eqF 1:(ltr_le_trans 2) //.
  rewrite lt_fromint (ltr_le_trans 1) //.
have := int_log_ub_lt b n _ _ => //.
by rewrite {1}n_eq_b2_il_bn_plus1.
qed.

(* connections of int_log and int_log_up with real log and floor/ceil *)

lemma int_log_floor_log (b n : int) :
  2 <= b => 1 <= n =>
  int_log b n = floor (log b%r n%r).
proof.
move => ge2_b ge1_n.
have [low_le high_le] := real_log_bounds b n _ _ => //.
case (b ^ int_log b n = n) => [b2ilbn_eq_n | b2ilbn_ne_n].
have ilu_eq_il_bn : int_log_up b n = int_log b n.
  by rewrite eq_sym int_log_int_log_up_eq_iff.
have -> : log b%r n%r = (int_log b n)%r.
  apply RealOrder.ler_anti.
  split => [| _ //]; by rewrite -ilu_eq_il_bn.
by rewrite from_int_floor.
rewrite (floorE (int_log b n)) //.
split => [// | _].
have -> : int_log b n + 1 = int_log_up b n.
  by rewrite /int_log_up b2ilbn_ne_n.
by rewrite real_log_ub_lt.
qed.

lemma int_log_up_ceil_log (b n : int) :
  2 <= b => 1 <= n =>
  int_log_up b n = ceil (log b%r n%r).
proof.
move => ge2_b ge1_n.
have [low_le high_le] := real_log_bounds b n _ _ => //.
case (b ^ int_log b n = n) => [b2ilbn_eq_n | b2ilbn_ne_n].
have ilu_eq_il_bn : int_log_up b n = int_log b n.
  by rewrite eq_sym int_log_int_log_up_eq_iff.
have -> : log b%r n%r = (int_log b n)%r.
  apply RealOrder.ler_anti.
  split => [| _ //]; by rewrite -ilu_eq_il_bn.
by rewrite from_int_ceil ilu_eq_il_bn.
rewrite (ceilE (int_log b n + 1)) //.
split => [/= | _].
rewrite RealOrder.ltr_def low_le /=.
case (log b%r n%r = (int_log b n)%r) => [contrad | //].
have // : b ^ (int_log b n) = n.
  rewrite -eq_fromint -RField.fromintXn 1:int_log_ge0 //.
  rewrite -rpow_nat 1:int_log_ge0 //.
  by rewrite le_fromint (ler_trans 2) //.
  rewrite -contrad rpowK 1:lt_fromint 1:(ltr_le_trans 2) //.
  rewrite eq_fromint gtr_eqF 1:ltzE //.
  by rewrite lt_fromint (ltr_le_trans 1).
have -> // : int_log b n + 1 = int_log_up b n.
  by rewrite /int_log_up b2ilbn_ne_n.
by rewrite /int_log_up b2ilbn_ne_n.
qed.

lemma int_log_up_distr_mul (b n m : int) :
  2 <= b => 1 <= n => 1 <= m =>
  int_log_up b n + int_log_up b m - 1 <=
  int_log_up b (n * m) <=
  int_log_up b n + int_log_up b m.
proof.
move => ge2_b ge1_n ge1_m.
have ge0_b : 0 <= b by rewrite (ler_trans 2).
have ge1_b : 1 <= b by rewrite (ler_trans 2).
have ge0_n : 0 <= n by rewrite (ler_trans 1).
have ge0_m : 0 <= m by rewrite (ler_trans 1).
have [[eq0_ilu_b_n eq1_n] |
      [ge1_ilu_b_n [b2ilu_b_n_min1_lt_n n_le_b2_ilu_b_n]]]
     := int_log_upP b n _ _ => //.
have [[eq0_ilu_b_m eq1_m] |
      [ge1_ilu_b_m [b2ilu_b_m_min1_lt_m m_le_b2_ilu_b_m]]]
     := int_log_upP b m _ _ => //.
rewrite eq0_ilu_b_n eq0_ilu_b_m eq1_n eq1_m /=.
have -> // : int_log_up b 1 = 0 by rewrite int_log_up_zero_iff.
rewrite eq0_ilu_b_n eq1_n /= ler_subl_addl ler_addr //.
have [[eq0_ilu_b_m eq1_m] |
      [ge1_ilu_b_m [b2ilu_b_m_min1_lt_m m_le_b2_ilu_b_m]]]
     := int_log_upP b m _ _ => //.
rewrite eq0_ilu_b_m eq1_m /= ler_subl_addl ler_addr //.
have nm_b2_lb_lt : b ^ (int_log_up b n + int_log_up b m - 2) < n * m.
  have -> :
    int_log_up b n + int_log_up b m - 2 =
    (int_log_up b n - 1) + (int_log_up b m - 1) by algebra.
  rewrite exprD_nneg 1:ler_subr_addr // 1:ler_subr_addr //.
  by rewrite ltr_pmul 1:expr_ge0 // 1:expr_ge0.
have nm_b2_ub_le : n * m <= b ^ (int_log_up b n + int_log_up b m).
  by rewrite exprD_nneg // 1:(ler_trans 1) // 1:(ler_trans 1) // ler_pmul.
case (b ^ (int_log_up b n + int_log_up b m - 1) < n * m) =>
  [b2_ilu_b_n_plus_ilu_b_m_min1_lt_nm | nm_le_b2_ilu_b_n_plus_ilu_b_m_min1].
have ilu_b_nm_eq_ilu_b_n_plus_ilu_b_m :
  int_log_up b (n * m) = int_log_up b n + int_log_up b m.
  rewrite (int_log_up_ge2_Puniq b (n * m)
          (int_log_up b n + int_log_up b m)) //.
  have -> : 2 = 1 + 1 by trivial.
  rewrite lez_add1r
          (ler_lt_trans (b ^ (int_log_up b n + int_log_up b m - 2)))
          1:exprn_ege1 //.
  have -> :
    int_log_up b n + int_log_up b m - 2 =
    (int_log_up b n - 1) + (int_log_up b m - 1) by algebra.
  rewrite addr_ge0 ler_subr_addl //.
  by rewrite (ler_trans (1 + 1)) // ler_add.
rewrite ilu_b_nm_eq_ilu_b_n_plus_ilu_b_m.
split => [| //].
by rewrite ler_subl_addr ler_addl.
rewrite -lerNgt in nm_le_b2_ilu_b_n_plus_ilu_b_m_min1.
have ilu_b_nm_eq_ilu_b_n_plus_ilu_b_m_min1 :
  int_log_up b (n * m) = int_log_up b n + int_log_up b m - 1.
  rewrite (int_log_up_ge2_Puniq b (n * m)
           (int_log_up b n + int_log_up b m - 1)) //.
  have -> : 2 = 1 + 1 by trivial.
  rewrite lez_add1r
          (ler_lt_trans (b ^ (int_log_up b n + int_log_up b m - 2))) //
          exprn_ege1 //.
  have -> :
    int_log_up b n + int_log_up b m - 2 =
    (int_log_up b n - 1) + (int_log_up b m - 1) by algebra.
  rewrite addr_ge0 ler_subr_addl //.
  rewrite ler_subr_addl /=.
  have -> : 2 = 1 + 1 by trivial.
  by rewrite ler_add.
split => [| _].
by rewrite ilu_b_nm_eq_ilu_b_n_plus_ilu_b_m_min1.
rewrite ilu_b_nm_eq_ilu_b_n_plus_ilu_b_m_min1.
by rewrite ler_subl_addr ler_addl.
qed.

lemma int_log_up_distr_mul_lb (b n m : int) :
  2 <= b => 1 <= n => 1 <= m =>
  int_log_up b n + int_log_up b m - 1 <= int_log_up b (n * m).
proof.
move => ge2_b ge1_n ge1_m.
have := int_log_up_distr_mul b n m _ _ _ => //.
qed.

lemma int_log_up_distr_mul_ub (b n m : int) :
  2 <= b => 1 <= n => 1 <= m =>
  int_log_up b (n * m) <= int_log_up b n + int_log_up b m.
proof.
move => ge2_b ge1_n ge1_m.
have := int_log_up_distr_mul b n m _ _ _ => //.
qed.

lemma int_log_divup_min1 (b n : int) :
  2 <= b => b <= n => n <= b ^ (int_log b n + 1) - b =>
  int_log b (n %%/ b) = int_log b n - 1.
proof.
move => ge2_b le_b_n le_n_b2il_n_plus1_min_b.
rewrite /(%%/).
case (b %| n) => [b_dvdz_n /= | not_b_dvdz_n].
by apply int_log_div.
have ge0_b : 0 <= b by rewrite (ler_trans 2).
have ge1_b : 1 <= b by rewrite (ler_trans 2).
have ge1_n : 1 <= n by rewrite (ler_trans b) // (ler_trans 2).
have ge1_il_n : 1 <= int_log b n by rewrite int_log_ge1_when_ge_b.
rewrite (int_logPuniq b (n %/ b + 1) (int_log b n - 1)) //=.
by rewrite ler_subr_addr.
have [#] _ := int_logP b n _ _ => //.
move : le_n_b2il_n_plus1_min_b.
have -> : int_log b n = (int_log b n - 1) + 1 by algebra.
pose p := int_log b n - 1.
have ge0_p : 0 <= p by rewrite /p ler_subr_addr.
have ge0_p_plus1 : 0 <= p + 1 by rewrite addz_ge0.
rewrite {1}(exprS _ p) // (mulrC _ (b ^ p)).
move => le_n_b2_p_plus1_plus1 b2p_tim_b_le_n _.
split => [/= | _].
have -> : b ^ p = b ^ p * b %/ b by rewrite mulzK // lt0r_neq0 1:ltzE.
by rewrite (ler_trans (n %/ b)) 1:leq_div2r // lez_addl.
rewrite -ltr_subr_addr ltz_divLR 1:ltzE //.
have -> : (b ^ (p + 1) - 1) * b = b ^ (p + 2) - b.
  have -> : p + 2 = (p + 1) + 1 by trivial.
  rewrite (exprS _ (p + 1)) //.
  algebra.
have n_ne_b2_p_plus2_min_b : n <> b ^ (p + 2) - b.
  move : not_b_dvdz_n.
  case (n = b ^ (p + 2) - b) => [-> | //].
  have -> : p + 2 = p + 1 + 1 by trivial.
  rewrite exprS //.
  have -> : b * b ^ (p + 1) - b = b * (b ^ (p + 1) - 1) by algebra.
  by rewrite dvdz_mulr 1:dvdzz.
by rewrite ltz_def eq_sym n_ne_b2_p_plus2_min_b.
qed.

lemma int_log2_divup_min1 (n : int) :
  2 <= n => n < 2 ^ (int_log 2 n + 1) - 1 =>
  int_log 2 (n %%/ 2) = int_log 2 n - 1.
proof.
move => ge2_n lt_n_two2_il_n_plus1_min1.
rewrite int_log_divup_min1 //.
have -> : 2 ^ (int_log 2 n + 1) - 2 = 2 ^ (int_log 2 n + 1) - 1 - 1.
  trivial.
rewrite ler_subr_addr.
by rewrite -ltzE.
qed.

lemma dvdz_gt_mul_implies_ge_next_mul (b n m : int) :
  1 <= b => m * b < n => b %| n => (m + 1) * b <= n.
proof.
move => ge1_b m_tim_b_lt_n b_dvdz_n.
have [cond_neq _] := dvdz_eq b n.
have -> : n = n %/ b * b by rewrite cond_neq.
by rewrite ler_pmul2r 1:ltzE // -ltzE ltz_divRL 1:ltzE.
qed.

lemma int_log_divup_eq (b n : int) :
  2 <= b => b <= n => b ^ (int_log b n + 1) - b < n =>
  int_log b (n %%/ b) = int_log b n.
proof.
move => ge2_b le_b_n b2il_n_plus1_min_b_lt_n.
have ge0_b : 0 <= b by rewrite (ler_trans 2).
have ge1_b : 1 <= b by rewrite (ler_trans 2).
have ge1_n : 1 <= n by rewrite (ler_trans b) // (ler_trans 2).
rewrite (int_logPuniq b (n %%/ b) (int_log b n)) //.
by rewrite int_log_ge0.
have [#] _ _ n_lt_b2_il_n_plus1 := int_logP b n _ _ => //.
split => [| _].
move : b2il_n_plus1_min_b_lt_n.
  have -> : b ^ (int_log b n + 1) - b = (b ^ int_log b n - 1) * b.
  rewrite exprS 1:int_log_ge0 //.
  algebra.
move => b2il_n_min1_tim_b_lt_n.
rewrite /(%%/).
case (b %| n) => [b_dvdz_n /= | not_b_dvdz_n].
rewrite lez_divRL 1:ltzE //.
have -> : b ^ int_log b n * b = ((b ^ int_log b n - 1) + 1) * b.
  algebra.
by rewrite dvdz_gt_mul_implies_ge_next_mul.
by rewrite -ler_subl_addr lez_divRL 1:ltzE // ltzW.
by rewrite (ler_lt_trans n) // int_div_up_le_self // (ler_trans b).
qed.

lemma int_log2_divup_eq (n : int) :
  2 <= n => n = 2 ^ (int_log 2 n + 1) - 1 =>
  int_log 2 (n %%/ 2) = int_log 2 n.
proof.
move => ge2_n n_eq_two2il_n_plus1_min1.
rewrite int_log_divup_eq // {2}n_eq_two2il_n_plus1_min1.
have -> : 2 ^ (int_log 2 n + 1) - 2 = 2 ^ (int_log 2 n + 1) - 1 - 1.
  trivial.
by rewrite ltzE.
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
by rewrite int_div2_lt_self_if_ge1.
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
by rewrite int_div2_up_lt_self_if_ge2.
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

lemma divpow2up_start (n : int) :
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
