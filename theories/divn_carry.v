(** * Carry arithmetic for Kummer's theorem *)
(** This file develops the floor-division addition identity and
    the carry predicate, culminating in the summed carry-count
    identity used to prove Kummer's theorem. *)

From mathcomp Require Import all_boot all_order.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The floor-division addition identity *)

Lemma divn_add a b m : 0 < m ->
  (a + b) %/ m = a %/ m + b %/ m + (m <= a %% m + b %% m).
Proof.
Admitted.

Lemma modn_add a b m : 0 < m ->
  (a + b) %% m = (a %% m + b %% m) %% m.
Proof.
Admitted.

Lemma divn_add_mod_bound a b m : 0 < m ->
  a %% m + b %% m < 2 * m.
Proof.
Admitted.

Lemma divn_add_mod_cases a b m : 0 < m ->
  (a %% m + b %% m) %/ m <= 1.
Proof.
Admitted.

Lemma carry_is_div a b m : 0 < m ->
  (m <= a %% m + b %% m) = ((a %% m + b %% m) %/ m == 1).
Proof.
Admitted.

(** ** The carry predicate *)

Definition carry p i a b := p ^ i <= a %% p ^ i + b %% p ^ i.

Lemma divn_add_carry p i n k :
  0 < p -> k <= n ->
  n %/ p ^ i = k %/ p ^ i + (n - k) %/ p ^ i + carry p i k (n - k).
Proof.
Admitted.

(** ** Summed carry-count identity *)

Lemma sum_divn_add_carry p n k b :
  prime p -> k <= n -> trunc_log p n < b ->
  \sum_(1 <= i < b.+1) (n %/ p ^ i) =
    \sum_(1 <= i < b.+1) (k %/ p ^ i) +
    \sum_(1 <= i < b.+1) ((n - k) %/ p ^ i) +
    \sum_(1 <= i < b.+1) carry p i k (n - k).
Proof.
Admitted.
