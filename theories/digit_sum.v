(** * Digit sums and the alternative Kummer formulation *)
(** This file defines base-p digit extraction and digit sums,
    then proves Kummer's theorem in its digit-sum form. *)

From mathcomp Require Import all_boot all_order.
From MathCompKummer Require Import divn_carry logn_bin.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Digit extraction *)

Definition digit p i n := (n %/ p ^ i) %% p.

Lemma digit_bound p i n : 1 < p -> digit p i n < p.
Proof. move=> hp; rewrite /digit ltn_pmod //; exact: ltnW. Qed.

Lemma trunc_log_div p n : 1 < p -> p <= n ->
  trunc_log p (n %/ p) = (trunc_log p n).-1.
Proof.
move=> hp hpn.
have hndp : 0 < n %/ p by rewrite divn_gt0 ?(ltnW hp).
have htl0 : 0 < trunc_log p n
  by rewrite trunc_log_gt0 hp /= -ltnS (ltn_predK hp).
have hpos : 0 < n by apply: leq_trans hpn; apply: ltnW.
have /andP [hlo hhi] := trunc_log_bounds hp hpos.
set k := trunc_log p n.
apply: trunc_log_eq => //.
rewrite (prednK htl0); apply/andP; split.
- by rewrite leq_divRL ?(ltnW hp) // -expnSr (prednK htl0).
- by rewrite ltn_divLR ?(ltnW hp) // -expnSr.
Qed.

Lemma digits_repr p n :
  1 < p -> 0 < n ->
  n = \sum_(0 <= i < (trunc_log p n).+1)
        digit p i n * p ^ i.
Proof.
move=> hp; elim/ltn_ind: n => n IH hn.
case: (ltnP n p) => hnp.
- have htl: trunc_log p n = 0
    by apply/eqP; rewrite trunc_log_eq0; apply/orP; right;
       rewrite -ltnS (ltn_predK hp).
  by rewrite htl big_nat1 /digit expn0 divn1 muln1 modn_small.
- have hndp : 0 < n %/ p by rewrite divn_gt0 ?(ltnW hp).
  have htl0 : 0 < trunc_log p n
    by rewrite trunc_log_gt0 hp /= -ltnS (ltn_predK hp).
  rewrite big_nat_recl // /digit expn0 divn1 muln1.
  rewrite {1}(divn_eq n p) addnC; congr (_ + _).
  have hIH := IH (n %/ p) (ltn_Pdiv hp hn) hndp.
  rewrite /digit in hIH.
  rewrite (trunc_log_div hp hnp) (prednK htl0) in hIH.
  rewrite {1}hIH big_distrl /=; apply: eq_big => // i _.
  by rewrite expnS divnMA -mulnA [p ^ i * p]mulnC.
Qed.

(** ** Digit sum *)

Definition digit_sum p n :=
  \sum_(0 <= i < (trunc_log p n).+1) digit p i n.

Lemma digit_sum_rec p n : 1 < p -> p <= n ->
  digit_sum p n = n %% p + digit_sum p (n %/ p).
Proof.
move=> hp hpn.
have hndp : 0 < n %/ p by rewrite divn_gt0 ?(ltnW hp).
have htl0 : 0 < trunc_log p n
  by rewrite trunc_log_gt0 hp /= -ltnS (ltn_predK hp).
rewrite /digit_sum big_nat_recl //.
rewrite /digit expn0 divn1; congr (_ + _).
rewrite (trunc_log_div hp hpn) (prednK htl0).
by apply: eq_bigr => i _; rewrite /digit expnS divnMA.
Qed.

Lemma logn_fact_rec p n :
  prime p -> 0 < n ->
  logn p n`! = n %/ p + logn p (n %/ p)`!.
Proof.
move=> hp hn.
have h1p := prime_gt1 hp.
set b := trunc_log p n.
rewrite (logn_fact_ext hp (n := n) (b := b.+1)) //.
rewrite big_ltn //= expn1; congr (_ + _).
case: (posnP (n %/ p)) => hndp.
- rewrite hndp fact0 logn1.
  rewrite big_nat_cond big1 // => i /andP [/andP [hi _] _].
  apply: divn_small.
  have hnp : n < p.
    have := divn_eq n p.
    by rewrite hndp mul0n add0n => ->;
       rewrite ltn_pmod // ltnW.
  apply: leq_trans hnp _; rewrite -[p]expn1.
  exact: leq_pexp2l (ltnW h1p) (ltnW hi).
- have hpn : p <= n
    by move: hndp; rewrite divn_gt0 // ltnW.
  have htl0 : 0 < b
    by rewrite /b trunc_log_gt0 h1p /=
       -ltnS (ltn_predK h1p).
  rewrite (logn_fact_ext hp (n := n %/ p) (b := b)) //.
  + rewrite big_add1 /=.
    by apply: eq_bigr => i _; rewrite expnS divnMA.
  + by rewrite (trunc_log_div h1p hpn) prednK.
Qed.

Lemma digit_sum_le p n : 1 < p -> digit_sum p n <= n.
Proof.
move=> hp; case: (posnP n) => [-> | hn].
  by rewrite /digit_sum trunc_log0 big_nat1
     /digit expn0 divn1 mod0n.
rewrite {2}(digits_repr hp hn) /digit_sum.
apply: leq_sum => i _; rewrite -{1}[digit p i n]muln1.
by apply: leq_mul => //; rewrite expn_gt0 ltnW.
Qed.

(** ** Legendre's formula via digit sums *)

Lemma legendre_digit_sum p n :
  prime p -> 0 < n ->
  p.-1 * logn p n`! = n - digit_sum p n.
Proof.
move=> hp; elim/ltn_ind: n => n IH hn.
have h1p := prime_gt1 hp.
case: (ltnP n p) => hnp.
- rewrite logn_fact //.
  rewrite big_nat_cond big1; last first.
    move=> i /andP [/andP [hi _] _]; apply: divn_small.
    apply: leq_trans hnp _; rewrite -[p]expn1.
    exact: leq_pexp2l (ltnW h1p) hi.
  rewrite muln0 /digit_sum.
  have ->: trunc_log p n = 0
    by apply/eqP; rewrite trunc_log_eq0; apply/orP;
       right; rewrite -ltnS (ltn_predK h1p).
  by rewrite big_nat1 /digit expn0 divn1 modn_small // subnn.
- have hndp : 0 < n %/ p by rewrite divn_gt0 ?(ltnW h1p).
  rewrite logn_fact_rec // mulnDr.
  rewrite (IH _ (ltn_Pdiv h1p hn) hndp).
  set q := n %/ p; set ds := digit_sum p q.
  have hds_le : ds <= q by apply: digit_sum_le.
  rewrite [digit_sum p n]digit_sum_rec //.
  rewrite /ds -/q.
  rewrite addnBA // subnDA {1}(divn_eq n p) addnK.
  rewrite -mulSnr prednK; last by exact: ltnW.
  by rewrite mulnC.
Qed.

(** ** Kummer's theorem via digit sums *)

Theorem kummer_digit_sum p n k :
  prime p -> k <= n -> 0 < k ->
  p.-1 * logn p 'C(n, k) =
    digit_sum p k + digit_sum p (n - k) - digit_sum p n.
Proof.
move=> hp hkn hk.
have h1p := prime_gt1 hp.
have hn : 0 < n by exact: leq_trans hk hkn.
case: (posnP (n - k)) => hnk.
+ move/eqP: hnk; rewrite subn_eq0 => hkn'.
  have heq : n = k by apply/eqP; rewrite eqn_leq hkn hkn'.
  rewrite heq subnn /digit_sum trunc_log0 big_nat1 /digit
    expn0 divn1 mod0n addn0 subnn logn_bin // subnn.
  by rewrite muln0.
+ suff hadd_eq : p.-1 * logn p 'C(n, k) + digit_sum p n =
    digit_sum p k + digit_sum p (n - k).
    by rewrite -hadd_eq addnK.
  apply/eqP.
  rewrite -(eqn_add2r (p.-1 * (logn p k`! + logn p (n - k)`!))).
  rewrite addnAC -mulnDr.
  have hfact : logn p 'C(n, k) + (logn p k`! + logn p (n - k)`!) = logn p n`!.
    rewrite -lognM ?fact_gt0 // -lognM ?muln_gt0 ?fact_gt0 ?bin_gt0 //.
    by rewrite bin_fact.
  rewrite hfact.
  rewrite addnC (legendre_digit_sum hp hn) subnKC; last exact: digit_sum_le.
  rewrite mulnDr addnACA.
  rewrite (legendre_digit_sum hp hk) subnKC; last exact: digit_sum_le.
  rewrite (legendre_digit_sum hp hnk) subnKC; last exact: digit_sum_le.
  by rewrite subnKC.
Qed.
