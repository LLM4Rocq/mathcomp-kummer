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
Admitted.

Lemma logn_fact_ext p n b :
  prime p -> trunc_log p n < b ->
  logn p n`! = \sum_(1 <= i < b.+1) (n %/ p ^ i).
Proof.
Admitted.

(** ** p-adic valuation of binomial coefficients *)

Lemma logn_bin p n k :
  prime p -> k <= n ->
  logn p 'C(n, k) = logn p n`! - logn p k`! - logn p (n - k)`!.
Proof.
Admitted.

Lemma logn_bin_via_sums p n k b :
  prime p -> k <= n -> trunc_log p n < b ->
  logn p 'C(n, k) =
    \sum_(1 <= i < b.+1) (n %/ p ^ i) -
    \sum_(1 <= i < b.+1) (k %/ p ^ i) -
    \sum_(1 <= i < b.+1) ((n - k) %/ p ^ i).
Proof.
Admitted.

(** ** Kummer's theorem *)

Theorem kummer p n k :
  prime p -> k <= n ->
  logn p 'C(n, k) =
    \sum_(1 <= i < (trunc_log p n).+2)
      carry p i k (n - k).
Proof.
Admitted.

Theorem kummer_card p n k b :
  prime p -> k <= n -> trunc_log p n < b ->
  logn p 'C(n, k) =
    #|[set i in 'I_b | carry p i.+1 k (n - k)]|.
Proof.
Admitted.
