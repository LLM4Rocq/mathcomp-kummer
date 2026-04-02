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
Proof. exact: divnD. Qed.

Lemma modn_add a b m : 0 < m ->
  (a + b) %% m = (a %% m + b %% m) %% m.
Proof. by move=> ?; rewrite modnDm. Qed.

Lemma divn_add_mod_bound a b m : 0 < m ->
  a %% m + b %% m < 2 * m.
Proof.
move=> hm; apply: (@leq_ltn_trans (a %% m + m)).
  by rewrite leq_add2l ltnW // ltn_pmod.
by rewrite mul2n -addnn ltn_add2r ltn_pmod.
Qed.

Lemma divn_add_mod_cases a b m : 0 < m ->
  (a %% m + b %% m) %/ m <= 1.
Proof.
move=> hm; rewrite -ltnS ltn_divLR //.
exact: divn_add_mod_bound.
Qed.

Lemma carry_is_div a b m : 0 < m ->
  (m <= a %% m + b %% m) = ((a %% m + b %% m) %/ m == 1).
Proof.
move=> hm; set x := _ + _; apply/idP/idP => [hle | /eqP hd].
- by apply/eqP/anti_leq; rewrite leq_divRL // mul1n hle
     divn_add_mod_cases.
- by rewrite -(mul1n m) -hd -leq_divRL.
Qed.

(** ** The carry predicate *)

Definition carry p i a b := p ^ i <= a %% p ^ i + b %% p ^ i.

Lemma divn_add_carry p i n k :
  0 < p -> k <= n ->
  n %/ p ^ i = k %/ p ^ i + (n - k) %/ p ^ i + carry p i k (n - k).
Proof.
by move=> hp hkn; rewrite /carry -divn_add ?expn_gt0 ?hp // subnKC.
Qed.

(** ** Summed carry-count identity *)

Lemma sum_divn_add_carry p n k b :
  prime p -> k <= n -> trunc_log p n < b ->
  \sum_(1 <= i < b.+1) (n %/ p ^ i) =
    \sum_(1 <= i < b.+1) (k %/ p ^ i) +
    \sum_(1 <= i < b.+1) ((n - k) %/ p ^ i) +
    \sum_(1 <= i < b.+1) carry p i k (n - k).
Proof.
move=> hp hkn _; rewrite -!big_split; apply: eq_bigr => i _.
exact: divn_add_carry (prime_gt0 hp) hkn.
Qed.
