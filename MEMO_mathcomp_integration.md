# Memo: Integration with MathComp / mathcomp-extra

## What already exists in MathComp

The following lemmas from `mathcomp.boot` are used directly in our proofs:

| Lemma | File | Statement |
|-------|------|-----------|
| `logn_fact` | `binomial.v` | `prime p -> logn p n`! = \sum_(1 <= k < n.+1) n %/ p ^ k` (Legendre's formula) |
| `bin_fact` | `binomial.v` | `k <= n -> 'C(n, k) * (k`! * (n - k)`!) = n`!` |
| `bin_gt0` | `binomial.v` | `(0 < 'C(n, k)) = (k <= n)` |
| `fact_gt0` | `binomial.v` | `0 < n`!` |
| `logn_fact` | `binomial.v` | Legendre's formula (see above) |
| `lognM` | `prime.v` | `0 < m -> 0 < n -> logn p (m * n) = logn p m + logn p n` |
| `pfactorK` | `prime.v` | `prime p -> logn p (p ^ n) = n` |
| `trunc_log_ltn` | `prime.v` | `1 < p -> n < p ^ (trunc_log p n).+1` |
| `trunc_log_bounds` | `prime.v` | `1 < p -> 0 < n -> p ^ trunc_log p n <= n` |
| `divnD` | `div.v` | `(a + b) %/ m = a %/ m + b %/ m + (m <= a %% m + b %% m)` |
| `divn_eq` | `div.v` | Euclidean division characterization |
| `ltn_pmod` | `div.v` | `0 < m -> n %% m < m` |

**Key point**: Legendre's formula (`logn_fact`) is already proved in MathComp. Our contribution starts from there.

## What exists in mathcomp-extra (thery/mathcomp-extra)

- `digitn.v` — base-p digit extraction and **Lucas' theorem** for binomial coefficients mod p.
  Lucas and Kummer are closely related: Lucas gives `'C(n,k) mod p` via digits,
  Kummer gives `v_p('C(n,k))` via carries. They could share digit infrastructure.

- No Kummer theorem, no carry predicate, no digit-sum Legendre reformulation.

## What we contribute (new content)

### Layer 1: Carry arithmetic (`divn_carry.v`)
- `carry p i a b` — the carry predicate: `p^i <= a %% p^i + b %% p^i`
- `divn_add_carry` — floor division splits as quotients + carry
- `sum_divn_add_carry` — summed version for Kummer

Note: `divn_add` is just a thin wrapper around MathComp's `divnD`. Same for `modn_add`.
These could be dropped upstream if the carry lemmas reference `divnD` directly.

### Layer 2: Kummer's theorem (`logn_bin.v`)
- `logn_bin` — `v_p('C(n,k)) = v_p(n!) - v_p(k!) - v_p((n-k)!)`
- `logn_bin_via_sums` — rewrite using Legendre sums
- `kummer` — **main theorem**: `v_p('C(n,k)) = sum of carries`
- `kummer_card` — cardinality form

### Layer 3: Corollaries (`logn_bin_extra.v`)
- `logn_bin_eq0` — primes larger than n don't divide C(n,k)
- `logn_bin_le1` — primes with p^2 > n appear at most once
- `logn_bin_le_trunc_log` — upper bound via trunc_log
- `logn_le_logn_bin_add` — lower bound: v_p(n) <= v_p(C(n,k)) + v_p(k)
- `logn_bin_prime_pow` — `v_p(C(p^m, k)) + v_p(k) = m`
- `logn2_fact_lt` — `v_2(n!) < n`

### Layer 4: Digit sums (`digit_sum.v`)
- `digit`, `digit_sum` — base-p digit extraction and sum
- `digits_repr` — digit representation: `n = sum of d_i * p^i`
- `legendre_digit_sum` — `(p-1) * v_p(n!) = n - s_p(n)`
- `kummer_digit_sum` — `(p-1) * v_p(C(n,k)) = s_p(k) + s_p(n-k) - s_p(n)`

## Where to submit

**Option A: mathcomp-extra** (recommended first step)
- Natural home: sits alongside Lucas theorem in `digitn.v`
- Lower friction: Laurent Thery maintains it, accepts PRs readily
- Could share/extend digit infrastructure with `digitn.v`
- Action: fork thery/mathcomp-extra, adapt build, submit PR

**Option B: core math-comp**
- The corollaries (`logn_bin_eq0`, `logn_bin_le1`, `logn_bin_prime_pow`) are
  fundamental enough for core. The carry machinery may be too specialized.
- Would need to split: corollaries in `binomial.v` or `prime.v`,
  Kummer + carries in a new file
- Higher bar: strict 80-char lines, naming review, community discussion

**Option C: hybrid**
- Submit useful corollaries to core math-comp (small, focused PR)
- Submit full Kummer + digit-sum machinery to mathcomp-extra

## Before submitting

1. Post on Rocq Zulip (math-comp stream) to ask where they'd prefer it
2. Check compatibility with `digitn.v` digit definitions
3. Ensure 80-char line limit, proper bullet indentation, `by`/`exact` closers
4. Remove thin wrappers (`divn_add`, `modn_add`) — use `divnD`/`modnDm` directly
5. Add file-level documentation headers
