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
Proof.
Admitted.

Lemma digits_repr p n :
  1 < p -> 0 < n ->
  n = \sum_(0 <= i < (trunc_log p n).+1) digit p i n * p ^ i.
Proof.
Admitted.

(** ** Digit sum *)

Definition digit_sum p n :=
  \sum_(0 <= i < (trunc_log p n).+1) digit p i n.

(** ** Legendre's formula via digit sums *)

Lemma legendre_digit_sum p n :
  prime p -> 0 < n ->
  p.-1 * logn p n`! = n - digit_sum p n.
Proof.
Admitted.

(** ** Kummer's theorem via digit sums *)

Theorem kummer_digit_sum p n k :
  prime p -> k <= n -> 0 < k ->
  p.-1 * logn p 'C(n, k) =
    digit_sum p k + digit_sum p (n - k) - digit_sum p n.
Proof.
Admitted.
