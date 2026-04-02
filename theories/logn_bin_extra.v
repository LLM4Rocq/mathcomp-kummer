(** * Corollaries of Kummer's theorem *)
(** Upper bounds and special cases for the p-adic valuation
    of binomial coefficients. *)

From mathcomp Require Import all_boot all_order.
From MathCompKummer Require Import divn_carry logn_bin.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma logn_bin_le_trunc_log p n k :
  prime p -> k <= n ->
  logn p 'C(n, k) <= trunc_log p n.
Proof.
move=> hp hkn; rewrite kummer //.
have h1p := prime_gt1 hp.
rewrite (@big_cat_nat _ _ _ (trunc_log p n).+1 1
  (trunc_log p n).+2) //= big_nat1 /carry.
have hn := trunc_log_ltn n h1p.
rewrite !modn_small ?subnKC //;
  [| exact: leq_ltn_trans (leq_subr k n) hn
   | exact: leq_ltn_trans hkn hn].
rewrite ltnNge in hn; rewrite (negbTE hn) addn0.
apply: (leq_trans (leq_sum _ _)).
  move=> i _; exact: leq_b1.
by rewrite sum_nat_const_nat muln1 subn1.
Qed.

Lemma logn_bin_eq0 p n k :
  prime p -> k <= n -> n < p ->
  logn p 'C(n, k) = 0.
Proof.
move=> hp hkn hnp; rewrite kummer //.
have h1p := prime_gt1 hp.
have htr : trunc_log p n = 0.
  apply/eqP; rewrite trunc_log_eq0; apply/orP; right.
  by rewrite -ltnS prednK // (ltn_trans _ h1p).
rewrite htr big_nat1 /carry expn1.
rewrite !modn_small ?subnKC //;
  [| exact: leq_ltn_trans (leq_subr _ _) hnp
   | exact: leq_ltn_trans hkn hnp].
by rewrite leqNgt (leq_ltn_trans _ hnp) //
   -subnKC // leq_addr.
Qed.

Lemma logn_bin_le1 p n k :
  prime p -> k <= n -> p * p > n ->
  logn p 'C(n, k) <= 1.
Proof.
move=> hp hkn hnpp.
have h1p := prime_gt1 hp.
have htr : trunc_log p n <= 1.
  case: (posnP n) => [->|hn]; first by rewrite trunc_log0.
  rewrite -ltnS -(ltn_exp2l _ _ h1p).
  apply: (leq_ltn_trans (trunc_logP h1p hn)).
  by rewrite expnS expn1.
exact: leq_trans (logn_bin_le_trunc_log hp hkn) htr.
Qed.

Lemma logn_le_logn_bin_add p n k :
  prime p -> k <= n -> 0 < k ->
  logn p n <= logn p 'C(n, k) + logn p k.
Proof.
move=> hp hkn hk.
have hmbd := mul_bin_diag n k.-1.
rewrite prednK // in hmbd.
have hn : 0 < n by exact: leq_trans hk hkn.
have hCnk : 0 < 'C(n, k) by rewrite bin_gt0.
have hkCnk : logn p (k * 'C(n, k)) =
  logn p k + logn p 'C(n, k) by rewrite lognM.
rewrite -hmbd in hkCnk.
have hCn1k1 : 0 < 'C(n.-1, k.-1)
  by rewrite bin_gt0 -!subn1 leq_sub2r.
rewrite lognM // in hkCnk.
rewrite addnC -hkCnk; exact: leq_addr.
Qed.

(* Helper: no carries when adding k.-1 and
   (p^m).-1 - k.-1 in base p *)
Lemma no_carry_pred_prime_pow p m k i :
  prime p -> 0 < k -> k <= p ^ m ->
  k.-1 %% p ^ i +
    ((p ^ m).-1 - k.-1) %% p ^ i < p ^ i.
Proof.
move=> hp hk hkpm.
have hpi : 0 < p ^ i
  by rewrite expn_gt0 prime_gt0.
have hpm : 0 < p ^ m
  by rewrite expn_gt0 prime_gt0.
have h1p := prime_gt1 hp.
have hkpm1 : k.-1 <= (p ^ m).-1
  by rewrite -!subn1 leq_sub2r.
set a := k.-1 %% p ^ i.
set b := ((p ^ m).-1 - k.-1) %% p ^ i.
have ha : a < p ^ i by exact: ltn_pmod.
have hb : b < p ^ i by exact: ltn_pmod.
have hab_le : a + b <= (p ^ m).-1.
  by apply: (leq_trans (leq_add (leq_mod _ _)
    (leq_mod _ _))); rewrite subnKC.
case: (ltnP (a + b) (p ^ i)) => //= hab_ge.
exfalso.
case: (leqP i m) => him.
- have [q hq] := dvdnP (dvdn_exp2l p him).
  have hq0 : 0 < q.
    by rewrite lt0n; apply/eqP => hq0;
    move: hpm; rewrite hq hq0 mul0n.
  have hpm1_mod :
    (p ^ m).-1 %% p ^ i = (p ^ i).-1.
    rewrite hq;
      case: q hq hq0 => // q' hq _.
    by rewrite mulSn -subn1 addnC -addnBA //
       modnMDl modn_small ?subn1 // ltn_predL.
  have hab_lt2 : a + b < 2 * p ^ i.
    by apply: (@leq_ltn_trans (p ^ i + b));
      [rewrite leq_add2r; exact: ltnW |
       rewrite mul2n -addnn ltn_add2l].
  have hab_mod2 :
    (a + b) %% p ^ i = a + b - p ^ i.
    rewrite {1}(_ : a + b =
      1 * p ^ i + (a + b - p ^ i));
      last by rewrite mul1n subnKC.
    by rewrite modnMDl modn_small //
       ltn_subLR // addnn -mul2n.
  have hmod : (a + b) %% p ^ i =
    (p ^ m).-1 %% p ^ i
    by rewrite /a /b modnDm subnKC.
  rewrite hab_mod2 hpm1_mod in hmod.
  have hab_eq : a + b = p ^ i + (p ^ i).-1
    by rewrite -(subnKC hab_ge) hmod.
  have : a + b <= (p ^ i).-1 + (p ^ i).-1
    by apply: leq_add;
       rewrite -ltnS prednK.
  rewrite hab_eq leq_add2r leqNgt
    ltn_predL hpi //.
- have hpmi : p ^ m < p ^ i
    by rewrite ltn_exp2l.
  move: (leq_ltn_trans hab_le
    (leq_ltn_trans (leq_pred _) hpmi)).
  by rewrite ltnNge hab_ge.
Qed.

Lemma logn_bin_prime_pow p m k :
  prime p -> 0 < k -> k <= p ^ m ->
  logn p 'C(p ^ m, k) + logn p k = m.
Proof.
move=> hp hk hkpm.
have hpm : 0 < p ^ m
  by rewrite expn_gt0 prime_gt0.
have hmbd := mul_bin_diag (p ^ m) k.-1.
rewrite prednK // in hmbd.
have hCnk : 0 < 'C(p ^ m, k)
  by rewrite bin_gt0.
have hCpred : 0 < 'C((p ^ m).-1, k.-1)
  by rewrite bin_gt0 -!subn1 leq_sub2r.
have hlognL :
  logn p (p ^ m * 'C((p ^ m).-1, k.-1)) =
  m + logn p 'C((p ^ m).-1, k.-1)
  by rewrite lognM // pfactorK.
have hlognR :
  logn p (k * 'C(p ^ m, k)) =
  logn p k + logn p 'C(p ^ m, k)
  by rewrite lognM.
rewrite -hmbd in hlognR.
rewrite hlognL in hlognR.
rewrite addnC -hlognR.
suffices -> :
  logn p 'C((p ^ m).-1, k.-1) = 0
  by rewrite addn0.
have hkpm1 : k.-1 <= (p ^ m).-1
  by rewrite -!subn1 leq_sub2r.
rewrite kummer //.
apply big1 => i _.
apply/eqP; rewrite /carry eqb0 -ltnNge.
exact: no_carry_pred_prime_pow hp hk hkpm.
Qed.

Lemma logn2_fact_lt n : 0 < n -> logn 2 n`! < n.
Proof.
move=> hn; rewrite logn_fact //.
suff haux : forall m, 0 < m ->
  \sum_(1 <= i < m.+1) m %/ 2 ^ i <= m.-1.
  by apply: leq_ltn_trans (haux n hn) _;
     rewrite ltn_predL.
elim/ltn_ind => n' IHn hn'.
case hn2 : (n' %/ 2) => [|k].
  have hn'_lt2 : n' < 2.
    have := divn_eq n' 2.
    rewrite hn2 mul0n add0n => hn'_eq.
    by rewrite hn'_eq; exact: ltn_pmod.
  have -> : n' = 1.
    by apply/eqP; rewrite eqn_leq hn' /=
       -ltnS hn'_lt2.
  by rewrite big_nat1 expn1 divn_small.
rewrite big_ltn //= expn1.
have hreindex :
  \sum_(2 <= i < n'.+1) n' %/ 2 ^ i =
  \sum_(1 <= i < n') (n' %/ 2) %/ 2 ^ i.
  rewrite big_add1 /=.
  by apply: eq_bigr => i _;
     rewrite expnS divnMA.
rewrite hreindex hn2.
have hn2' : 0 < n' %/ 2 by rewrite hn2.
have hIH :=
  IHn _ (ltn_Pdiv (isT : 1 < 2) hn') hn2'.
rewrite hn2 in hIH.
have htail :
  \sum_(1 <= i < n') k.+1 %/ 2 ^ i <= k.
  apply: leq_trans hIH.
  case: (leqP n' k.+2) => hcmp.
  - rewrite [X in _ <= X](@big_cat_nat _ _ _
      n' 1 k.+2) //=.
    exact: leq_addr.
  - rewrite (@big_cat_nat _ _ _ k.+2
      1 n') //=; last by exact: ltnW.
    rewrite [X in _ + X <= _]big_nat_cond
      [X in _ + X <= _]big1 ?addn0 //.
    move=> i /andP [/andP [hi _] _].
    apply: divn_small.
    apply: (leq_ltn_trans
      (ltnW (ltn_expl k.+1 (isT : 1 < 2)))).
    by rewrite ltn_exp2l.
apply: leq_trans (leq_add (leqnn _) htail) _.
have h : (n' %/ 2).*2 <= n'
  by rewrite -muln2 leq_divM.
rewrite hn2 doubleS in h.
by rewrite -ltnS (prednK hn') addnC addnS addnn.
Qed.
