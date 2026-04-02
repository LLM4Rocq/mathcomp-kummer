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
Admitted.

Lemma logn_bin_eq0 p n k :
  prime p -> k <= n -> n < p ->
  logn p 'C(n, k) = 0.
Proof.
Admitted.

Lemma logn_bin_le1 p n k :
  prime p -> k <= n -> p * p > n ->
  logn p 'C(n, k) <= 1.
Proof.
Admitted.

Lemma logn_le_logn_bin_add p n k :
  prime p -> k <= n -> 0 < k ->
  logn p n <= logn p 'C(n, k) + logn p k.
Proof.
Admitted.

Lemma logn_bin_prime_pow p m k :
  prime p -> 0 < k -> k <= p ^ m ->
  logn p 'C(p ^ m, k) + logn p k = m.
Proof.
Admitted.

Lemma logn2_fact_lt n : 0 < n -> logn 2 n`! < n.
Proof.
Admitted.
