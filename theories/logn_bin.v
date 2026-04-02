(** * From Legendre's formula to Kummer's theorem *)
(** This file connects the p-adic valuation of binomial coefficients
    to carry counts, proving Kummer's theorem. *)

From mathcomp Require Import all_boot all_order.
From MathCompKummer Require Import divn_carry.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Extending Legendre sums to a common bound *)

Lemma divn_small_pow p i n :
  1 < p -> trunc_log p n < i -> n %/ p ^ i = 0.
Proof.
move=> hp hi; apply/divn_small/(leq_trans (trunc_log_ltn n hp)).
exact: leq_pexp2l (ltnW hp) hi.
Qed.

Lemma logn_fact_ext p n b :
  prime p -> trunc_log p n < b ->
  logn p n`! = \sum_(1 <= i < b.+1) (n %/ p ^ i).
Proof.
move=> hp hb; rewrite logn_fact.
have h1p := prime_gt1 hp.
have htln : forall i, trunc_log p n < i -> n %/ p ^ i = 0.
  by move=> i; exact: divn_small_pow.
case: (leqP n.+1 b.+1) => hnb.
- rewrite [RHS](@big_cat_nat _ _ _ n.+1 1 b.+1) //=.
  rewrite [X in _ = _ + X]big_nat_cond
          [X in _ = _ + X]big1 ?addn0 //.
  move=> i /andP [/andP [hi _] _]; apply: htln.
  suff hle: trunc_log p n <= n
    by exact: leq_ltn_trans hle hi.
  case: {hi hb hnb} n => [|n']; first by rewrite trunc_log0.
  exact: leq_trans (ltnW (ltn_expl _ h1p))
                    (trunc_logP h1p (isT : 0 < n'.+1)).
- rewrite (@big_cat_nat _ _ _ b.+1 1 n.+1) //=;
    last exact: ltnW.
  rewrite [X in _ + X = _]big_nat_cond
          [X in _ + X = _]big1 ?addn0 //.
  move=> i /andP [/andP [hi _] _].
  by apply: htln; apply: ltn_trans hb hi.
- exact: hp.
Qed.

(** ** p-adic valuation of binomial coefficients *)

Lemma logn_bin p n k :
  prime p -> k <= n ->
  logn p 'C(n, k) = logn p n`! - logn p k`! - logn p (n - k)`!.
Proof.
move=> hp hkn.
have hbin := bin_fact hkn.
have hCgt0 : 0 < 'C(n, k) by rewrite bin_gt0.
have hkfgt0 : 0 < k`! * (n - k)`!
  by rewrite muln_gt0 !fact_gt0.
have hlog := lognM p hCgt0 hkfgt0.
rewrite hbin in hlog.
rewrite lognM ?fact_gt0 // in hlog.
by rewrite hlog -subnDA addnK.
Qed.

Lemma logn_bin_via_sums p n k b :
  prime p -> k <= n -> trunc_log p n < b ->
  logn p 'C(n, k) =
    \sum_(1 <= i < b.+1) (n %/ p ^ i) -
    \sum_(1 <= i < b.+1) (k %/ p ^ i) -
    \sum_(1 <= i < b.+1) ((n - k) %/ p ^ i).
Proof.
move=> hp hkn hb.
rewrite logn_bin //.
rewrite (logn_fact_ext hp hb).
have hkb : trunc_log p k < b
  by apply: leq_ltn_trans (leq_trunc_log _ hkn) hb.
rewrite (logn_fact_ext hp hkb).
have hnkb : trunc_log p (n - k) < b
  by apply: leq_ltn_trans (leq_trunc_log _ (leq_subr k n)) hb.
by rewrite (logn_fact_ext hp hnkb).
Qed.

(** ** Kummer's theorem *)

Theorem kummer p n k :
  prime p -> k <= n ->
  logn p 'C(n, k) =
    \sum_(1 <= i < (trunc_log p n).+2)
      carry p i k (n - k).
Proof.
move=> hp hkn.
have hb : trunc_log p n < (trunc_log p n).+1 by [].
rewrite (logn_bin_via_sums hp hkn hb).
have := sum_divn_add_carry hp hkn hb.
set Sn := \sum_(1 <= _ < _) (n %/ _).
set Sk := \sum_(1 <= _ < _) (k %/ _).
set Snk := \sum_(1 <= _ < _) ((n - k) %/ _).
set Sc := \sum_(1 <= _ < _) carry _ _ _ _.
move=> h; rewrite h.
rewrite /Sk /Sc /Snk.
set x := \sum_(1 <= _ < _) (k %/ _).
set y := \sum_(1 <= _ < _) carry _ _ _ _.
set z := \sum_(1 <= _ < _) ((n - k) %/ _).
by rewrite addnAC -subnDA -[x + y + z]addnA
   [y + z]addnC addnA addKn.
Qed.

Theorem kummer_card p n k b :
  prime p -> k <= n -> trunc_log p n < b ->
  logn p 'C(n, k) =
    #|[set i in 'I_b | carry p i.+1 k (n - k)]|.
Proof.
move=> hp hkn hb.
rewrite kummer //.
transitivity (\sum_(1 <= i < b.+1) carry p i k (n - k)).
  (* Extend carry sum: extra terms are 0 *)
  have h1p := prime_gt1 hp.
  rewrite [RHS](@big_cat_nat _ _ _
    (trunc_log p n).+2 1 b.+1) //=.
  rewrite [X in _ = _ + X]big_nat_cond
          [X in _ = _ + X]big1 ?addn0 //.
  move=> i /andP [/andP [hi _] _].
  rewrite /carry; case: leqP => // hle.
  have hpi : n < p ^ i.
    apply: leq_trans (trunc_log_ltn n h1p) _.
    exact: leq_pexp2l (ltnW h1p) (ltnW hi).
  have hlt: k %% p ^ i + (n - k) %% p ^ i < p ^ i.
    rewrite !modn_small ?subnKC //;
      [exact: leq_ltn_trans (leq_subr k n) hpi |
       exact: leq_ltn_trans hkn hpi].
  by move: (leq_ltn_trans hle hlt); rewrite ltnn.
(* Convert sum of bools to cardinality *)
have ->: 1 = 0 + 1 by [].
rewrite big_addn subn1 /= big_mkord.
under eq_bigr => i _ do rewrite addn1.
rewrite -sum1dep_card.
rewrite -[LHS]big_mkcond /=.
by apply: eq_bigr => i _; case: (carry _ _ _ _).
Qed.
