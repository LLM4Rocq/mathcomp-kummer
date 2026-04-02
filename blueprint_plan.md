# Blueprint plan: Kummer's theorem in MathComp via `rocqblueprint`

## 1. Project setup

### 1.1 Repository structure

```
mathcomp-kummer/
├── _CoqProject
├── rocq-mathcomp-kummer.opam
├── Makefile
├── .gitmodules                       # coqdocjs submodule
├── coqdocjs/                         # submodule for doc rendering
├── home_page/
│   └── index.html                    # landing page
├── theories/
│   ├── divn_carry.v                  # Phase 1: divn_add, carry arithmetic
│   ├── logn_bin.v                    # Phase 2-3: Kummer's theorem
│   ├── logn_bin_extra.v             # Phase 3.2: corollaries
│   └── digit_sum.v                  # Phase 4: digit sum formulation
├── blueprint/
│   └── src/
│       ├── web.tex                   # plasTeX entry point
│       ├── print.tex                 # xelatex entry point
│       ├── macros/
│       │   ├── common.tex            # shared macros
│       │   ├── web.tex               # web-only macros
│       │   └── print.tex             # print-only macros
│       ├── content.tex               # main blueprint (imports chapters)
│       ├── ch_existing.tex           # Chapter 1: existing MathComp API
│       ├── ch_carry.tex              # Chapter 2: carry arithmetic
│       ├── ch_legendre.tex           # Chapter 3: Legendre ↔ binomials
│       ├── ch_kummer.tex             # Chapter 4: Kummer's theorem
│       ├── ch_corollaries.tex        # Chapter 5: corollaries
│       └── ch_digits.tex             # Chapter 6: digit sums (optional)
└── .github/
    └── workflows/
        └── blueprint.yml             # CI: build docs + blueprint
```

### 1.2 Initialization steps

```bash
# 1. Create the project
mkdir mathcomp-kummer && cd mathcomp-kummer
git init

# 2. Set up _CoqProject
cat > _CoqProject << 'EOF'
-R theories MathCompKummer
theories/divn_carry.v
theories/logn_bin.v
theories/logn_bin_extra.v
theories/digit_sum.v
EOF

# 3. Install rocqblueprint
pip install rocqblueprint

# 4. Initialize the blueprint (interactive wizard)
rocqblueprint new
# → Set home URL, doc URL, github URL
# → This creates blueprint/src/ with template files

# 5. Add coqdocjs submodule for documentation rendering
git submodule add https://github.com/rocq-community/coqdocjs.git coqdocjs
```

### 1.3 `_CoqProject` dependencies

```
-R theories MathCompKummer
-arg -w -arg -notation-overridden
theories/divn_carry.v
theories/logn_bin.v
theories/logn_bin_extra.v
theories/digit_sum.v
```

Each `.v` file opens with:
```coq
From mathcomp Require Import all_ssreflect.
```

---

## 2. Blueprint content architecture

The `content.tex` file is the mathematical blueprint — a LaTeX document
using `rocqblueprint` macros that generates both a readable web document
and an interactive dependency graph. Each definition/lemma/theorem gets:

- A `\label{...}` for cross-referencing
- A `\rocq{Namespace.identifier}` linking to the Rocq declaration
- A `\uses{label1, label2, ...}` declaring dependencies (drives the graph)
- A `\rocqok` tag once the Rocq proof compiles

Below is the complete list of blueprint nodes, organized by chapter.
Items marked **[MC]** already exist in MathComp and appear as
"pre-existing" definition/lemma nodes. Items marked **[NEW]** are to be
formalized.

---

## 3. Chapter-by-chapter blueprint content

### Chapter 1: Existing MathComp infrastructure (`ch_existing.tex`)

These nodes document the MathComp API we depend on. They are all marked
`\rocqok` from the start and serve as roots of the dependency graph.

| Label | Kind | MathComp identifier | Description |
|---|---|---|---|
| `def:logn` | Definition | `logn` | p-adic valuation `logn p m` |
| `def:trunc_log` | Definition | `trunc_log` | Floor of log_p(n) |
| `def:binomial` | Definition | `bin` | Binomial coefficient `'C(n, k)` |
| `def:factorial` | Definition | `factorial` | Factorial `n!` |
| `lem:lognE` | Lemma | `lognE` | Recursive characterization of `logn` |
| `lem:lognM` | Lemma | `lognM` | `logn p (m * n) = logn p m + logn p n` |
| `lem:pfactor_dvdn` | Lemma | `pfactor_dvdn` | `(p^n \| m) = (n <= logn p m)` |
| `lem:pfactorK` | Lemma | `pfactorK` | `logn p (p^n) = n` |
| `lem:logn_count_dvd` | Lemma | `logn_count_dvd` | `logn p n = Σ (p^k \| n)` |
| `lem:trunc_log_bounds` | Lemma | `trunc_log_bounds` | `p^k <= n < p^(k+1)` |
| `lem:trunc_log_ltn` | Lemma | `trunc_log_ltn` | `n < p^(trunc_log p n + 1)` |
| `lem:logn_fact` | Lemma | `logn_fact` | Legendre: `logn p n! = Σ ⌊n/p^k⌋` |
| `lem:bin_fact` | Lemma | `bin_fact` | `C(n,k) * k! * (n-k)! = n!` |
| `lem:bin_gt0` | Lemma | `bin_gt0` | `(0 < C(n,k)) = (k <= n)` |
| `lem:fact_gt0` | Lemma | `fact_gt0` | `0 < n!` |
| `lem:divn_eq` | Lemma | `divn_eq` | `n = (n %/ d) * d + n %% d` |
| `lem:ltn_mod` | Lemma | `ltn_mod` | `(n %% d < d) = (0 < d)` |
| `lem:divn_small` | Lemma | `divn_small` | `m < d -> m %/ d = 0` |
| `lem:modnMDl` | Lemma | `modnMDl` | `(p * q + r) %% p = r %% p` |
| `lem:divnMDl` | Lemma | `divnMDl` | `(p * q + r) %/ p = q + r %/ p` |

### Chapter 2: Carry arithmetic (`ch_carry.tex`) ✅ COMPLETE

| Label | Kind | File | Description | Uses | Status |
|---|---|---|---|---|---|
| `def:carry` | Definition **[NEW]** | `divn_carry.v` | `carry p i a b := p^i <= a %% p^i + b %% p^i` | `def:binomial` | `\rocqok` |
| `lem:divn_add` | Lemma **[NEW]** | `divn_carry.v` | `(a+b) %/ m = a %/ m + b %/ m + (m <= a %% m + b %% m)` | `lem:divn_eq`, `lem:ltn_mod`, `lem:divn_small`, `lem:divnMDl` | `\rocqok` |
| `lem:modn_add` | Lemma **[NEW]** | `divn_carry.v` | `(a+b) %% m = (a %% m + b %% m) %% m` | `lem:divn_eq`, `lem:modnMDl` | `\rocqok` |
| `lem:divn_add_mod_bound` | Lemma **[NEW]** | `divn_carry.v` | `a %% m + b %% m < 2 * m` | `lem:ltn_mod` | `\rocqok` |
| `lem:divn_add_mod_cases` | Lemma **[NEW]** | `divn_carry.v` | `(a %% m + b %% m) %/ m ∈ {0, 1}` | `lem:divn_add_mod_bound`, `lem:divn_small` | `\rocqok` |
| `lem:carry_is_div` | Lemma **[NEW]** | `divn_carry.v` | `(m <= a%%m + b%%m) = (a%%m + b%%m) %/ m` | `lem:divn_add_mod_cases` | `\rocqok` |
| `lem:divn_add_carry` | Lemma **[NEW]** | `divn_carry.v` | `n %/ p^i = k %/ p^i + (n-k) %/ p^i + carry p i k (n-k)` for `k <= n` | `lem:divn_add`, `def:carry` | `\rocqok` |
| `lem:sum_divn_add_carry` | Lemma **[NEW]** | `divn_carry.v` | summing `divn_add_carry` over `i ∈ [1, b)`: the carry-count identity | `lem:divn_add_carry` | `\rocqok` |

### Chapter 3: Connecting Legendre to binomials (`ch_legendre.tex`)

| Label | Kind | File | Description | Uses |
|---|---|---|---|---|
| `lem:divn_small_pow` | Lemma **[NEW]** | `logn_bin.v` | `trunc_log p n < i -> n %/ p^i = 0` | `lem:trunc_log_ltn`, `lem:divn_small` |
| `lem:logn_fact_ext` | Lemma **[NEW]** | `logn_bin.v` | Extend Legendre sums to a common upper bound b | `lem:logn_fact`, `lem:divn_small_pow` |
| `lem:logn_bin` | Lemma **[NEW]** | `logn_bin.v` | `logn p C(n,k) = logn p n! - logn p k! - logn p (n-k)!` | `lem:bin_fact`, `lem:lognM`, `lem:bin_gt0`, `lem:fact_gt0` |
| `lem:logn_bin_via_sums` | Lemma **[NEW]** | `logn_bin.v` | `logn p C(n,k) = Σ ⌊n/p^i⌋ - Σ ⌊k/p^i⌋ - Σ ⌊(n-k)/p^i⌋` | `lem:logn_bin`, `lem:logn_fact_ext` |

### Chapter 4: Kummer's theorem (`ch_kummer.tex`)

| Label | Kind | File | Description | Uses |
|---|---|---|---|---|
| `thm:kummer` | **Theorem [NEW]** | `logn_bin.v` | `logn p C(n,k) = Σ_{i=1}^{b} carry p i k (n-k)` (Kummer) | `lem:logn_bin_via_sums`, `lem:sum_divn_add_carry` |
| `thm:kummer_card` | Theorem **[NEW]** | `logn_bin.v` | Cardinality formulation: `logn p C(n,k) = #|{i | carry p i k (n-k)}|` | `thm:kummer` |

### Chapter 5: Corollaries (`ch_corollaries.tex`)

| Label | Kind | File | Description | Uses |
|---|---|---|---|---|
| `lem:logn_bin_le_trunc_log` | Lemma **[NEW]** | `logn_bin_extra.v` | `logn p C(n,k) <= trunc_log p n` | `thm:kummer`, `lem:trunc_log_bounds` |
| `lem:logn_bin_eq0` | Lemma **[NEW]** | `logn_bin_extra.v` | `n < p -> logn p C(n,k) = 0` | `thm:kummer` |
| `lem:logn_bin_le1` | Lemma **[NEW]** | `logn_bin_extra.v` | `p*p > n -> logn p C(n,k) <= 1` | `thm:kummer`, `lem:trunc_log_bounds` |
| `lem:logn_le_logn_bin_add` | Lemma **[NEW]** | `logn_bin_extra.v` | `logn p n <= logn p C(n,k) + logn p k` | `lem:logn_bin`, `lem:bin_fact` |
| `lem:logn_bin_prime_pow` | Lemma **[NEW]** | `logn_bin_extra.v` | `logn p C(p^n, k) + logn p k = n` for `0 < k <= p^n` | `thm:kummer`, `lem:pfactorK` |
| `lem:logn2_fact_lt` | Lemma **[NEW]** | `logn_bin_extra.v` | `logn 2 n! < n` | `lem:logn_fact` |

### Chapter 6: Digit sums (optional) (`ch_digits.tex`)

| Label | Kind | File | Description | Uses |
|---|---|---|---|---|
| `def:digit` | Definition **[NEW]** | `digit_sum.v` | `digit p i n := (n %/ p^i) %% p` | |
| `def:digit_sum` | Definition **[NEW]** | `digit_sum.v` | `digit_sum p n := Σ digit p i n` | `def:digit` |
| `lem:digits_repr` | Lemma **[NEW]** | `digit_sum.v` | `n = Σ digit(p,i,n) * p^i` | `def:digit`, `lem:divn_eq` |
| `lem:digit_bound` | Lemma **[NEW]** | `digit_sum.v` | `digit p i n < p` | `def:digit`, `lem:ltn_mod` |
| `lem:legendre_digit_sum` | Lemma **[NEW]** | `digit_sum.v` | `(p-1) * logn p n! = n - digit_sum p n` | `lem:logn_fact`, `def:digit_sum` |
| `thm:kummer_digit_sum` | Theorem **[NEW]** | `digit_sum.v` | `(p-1) * logn p C(n,k) = s_p(k) + s_p(n-k) - s_p(n)` | `thm:kummer`, `lem:legendre_digit_sum` |

---

## 4. Dependency graph overview

The dependency graph will have this shape (automatically generated by
`rocqblueprint` from the `\uses{...}` annotations):

```
                   ┌─── divn_eq ───┐
                   │               │
              divn_small      ltn_mod
                   │               │
                   └──── divn_add ─┘
                            │
                     divn_add_carry
                            │
                    sum_divn_add_carry
                            │
    logn_fact ──→ logn_bin_via_sums ←── logn_bin ←── bin_fact + lognM
                            │
                         kummer  ◀══════════════ MAIN THEOREM
                        ╱  │  ╲
                       ╱   │   ╲
        logn_bin_le1  │  logn_bin_prime_pow
                      │
              kummer_digit_sum ←── legendre_digit_sum
```

---

## 5. Sample `content.tex` (main entry point)

```latex
\chapter{Existing MathComp infrastructure}
\input{ch_existing}

\chapter{Carry arithmetic}
\input{ch_carry}

\chapter{Connecting Legendre's formula to binomial coefficients}
\input{ch_legendre}

\chapter{Kummer's theorem}
\input{ch_kummer}

\chapter{Corollaries for binomial factorizations}
\input{ch_corollaries}

\chapter{Digit sums and the alternative Kummer formulation}
\input{ch_digits}
```

---

## 6. Sample LaTeX for key nodes

### 6.1 An existing MathComp lemma (root node)

```latex
\begin{lemma}[Legendre's formula]
  \label{lem:logn_fact}
  \rocq{logn_fact}  % link to MathComp's binomial.v
  \rocqok           % already proven
  Let $p$ be prime and $n \in \mathbb{N}$. Then
  \[
    v_p(n!) = \sum_{k=1}^{b} \left\lfloor \frac{n}{p^k} \right\rfloor
  \]
  for any $b$ such that $p^b > n$.
\end{lemma}
```

### 6.2 The core new lemma

```latex
\begin{lemma}[Floor-division addition identity]
  \label{lem:divn_add}
  \uses{lem:divn_eq, lem:ltn_mod, lem:divn_small, lem:divnMDl}
  \rocq{MathCompKummer.divn_carry.divn_add}
  Let $m > 0$. Then for all $a, b \in \mathbb{N}$,
  \[
    \left\lfloor \frac{a+b}{m} \right\rfloor
    = \left\lfloor \frac{a}{m} \right\rfloor
    + \left\lfloor \frac{b}{m} \right\rfloor
    + [m \leq (a \bmod m) + (b \bmod m)]
  \]
  where $[\cdot]$ denotes the Iverson bracket.
  \begin{proof}
    Write $a = qm + r$ and $b = q'm + r'$ with $0 \leq r, r' < m$.
    Then $a + b = (q + q')m + (r + r')$. Since $0 \leq r + r' < 2m$,
    we have $\lfloor(r+r')/m\rfloor \in \{0, 1\}$, and it equals $1$
    exactly when $r + r' \geq m$.
  \end{proof}
\end{lemma}
```

### 6.3 Kummer's theorem

```latex
\begin{theorem}[Kummer's theorem]
  \label{thm:kummer}
  \uses{lem:logn_bin_via_sums, lem:sum_divn_add_carry}
  \rocq{MathCompKummer.logn_bin.kummer}
  Let $p$ be prime and $0 \leq k \leq n$. Then
  \[
    v_p\!\binom{n}{k} = \#\bigl\{
      i \geq 1 \;\big|\; p^i \leq (k \bmod p^i) + ((n-k) \bmod p^i)
    \bigr\},
  \]
  i.e., the $p$-adic valuation of $\binom{n}{k}$ equals the number of
  carries when adding $k$ and $n-k$ in base $p$.
  \begin{proof}
    Combine Lemma~\ref{lem:logn_bin_via_sums} (expressing $v_p\binom{n}{k}$
    as a difference of Legendre sums) with Lemma~\ref{lem:sum_divn_add_carry}
    (the carry-count identity for summed floor divisions).
  \end{proof}
\end{theorem}
```

### 6.4 A not-yet-proven node with discussion link

```latex
\begin{theorem}[Kummer via digit sums]
  \label{thm:kummer_digit_sum}
  \uses{thm:kummer, lem:legendre_digit_sum}
  \rocq{MathCompKummer.digit_sum.kummer_digit_sum}
  \discussion{https://github.com/YOUR_USER/mathcomp-kummer/issues/3}
  Let $p$ be prime and $0 \leq k \leq n$. Then
  \[
    (p-1) \cdot v_p\!\binom{n}{k}
    = s_p(k) + s_p(n-k) - s_p(n),
  \]
  where $s_p(m) = \sum_{i \geq 0} d_i$ is the sum of the base-$p$
  digits of $m$.
\end{theorem}
```

---

## 7. Mapping to Mathlib: what each node translates

| Mathlib theorem | Blueprint label | Chapter |
|---|---|---|
| `Nat.emultiplicity_eq_card_pow_dvd` | `lem:logn_count_dvd` **[MC]** | 1 |
| `Nat.Prime.multiplicity_factorial` | `lem:logn_fact` **[MC]** | 1 |
| `Nat.Prime.multiplicity_factorial_mul` | derive from `lem:logn_fact` | 3 |
| `Nat.Prime.pow_dvd_factorial_iff` | derive from `lem:pfactor_dvdn` + `lem:logn_fact` | 1 |
| `Nat.Prime.emultiplicity_choose` | `thm:kummer` **[NEW]** | 4 |
| `Nat.Prime.emultiplicity_choose_prime_pow_add` | `lem:logn_bin_prime_pow` **[NEW]** | 5 |
| `Nat.Prime.emultiplicity_choose_prime_pow` | corollary of above **[NEW]** | 5 |
| `Nat.multiplicity_two_factorial_lt` | `lem:logn2_fact_lt` **[NEW]** | 5 |
| `Nat.factorization_choose_le_log` | `lem:logn_bin_le_trunc_log` **[NEW]** | 5 |
| `Nat.factorization_choose_le_one` | `lem:logn_bin_le1` **[NEW]** | 5 |
| `Nat.factorization_choose_eq_zero_of_lt` | `lem:logn_bin_eq0` **[NEW]** | 5 |
| `sub_one_mul_padicValNat_choose_eq_sub_sum_digits` | `thm:kummer_digit_sum` **[NEW]** | 6 |

---

## 8. CI workflow (`.github/workflows/blueprint.yml`)

The `rocqblueprint new` wizard generates a template. Key steps:

1. **Install Rocq + MathComp** via opam
2. **Build Rocq project**: `make` (from `_CoqProject`)
3. **Build coqdoc**: `make html` (using coqdocjs)
4. **Build blueprint**: `rocqblueprint web` (generates HTML from LaTeX)
5. **Build PDF**: `rocqblueprint pdf` (optional, requires TeX)
6. **Deploy** to GitHub Pages

Future: once `rocq-checkdecls` is stable (via coq-lsp), add a step
that verifies every `\rocq{...}` declaration actually exists in the
compiled project.

---

## 9. Development workflow

### Phase 1: Write the blueprint first (1–2 days)

1. Write all the LaTeX in `blueprint/src/ch_*.tex`
2. Mark existing MathComp lemmas as `\rocqok`
3. Leave new lemmas/theorems without `\rocqok`
4. Build and deploy: the dependency graph shows red/orange nodes for
   unproven items

### Phase 2: Formalize bottom-up, following the graph (1–3 weeks)

1. ~~Start with leaf nodes in Chapter 2 (`divn_add` and friends)~~ ✅ Done
2. Each time a Rocq proof compiles, add `\rocqok` to the corresponding
   LaTeX node
3. The dependency graph progressively turns green
4. Work up through ~~Chapters~~ 3 → 4 → 5 → 6
   - Chapter 2 (`divn_carry.v`): **8/8 nodes complete** (all `\rocqok`)
   - Chapter 3 (`logn_bin.v`): 0/4 — next target
   - Chapter 4 (`logn_bin.v`): 0/2
   - Chapter 5 (`logn_bin_extra.v`): 0/6
   - Chapter 6 (`digit_sum.v`): 0/6

### Phase 3: LLM-assisted acceleration (ongoing)

Use `rocq-mcp` / Claude Code to:
- Auto-generate proof sketches for arithmetic lemmas (Phase 1 nodes)
- Port proof strategies from Mathlib's `Data.Nat.Multiplicity.lean`
- Run `rocq_step_multi` to explore tactic spaces for stuck goals

Track LLM vs. human contribution per node for a potential ITP paper.

---

## 10. Node count summary

| Category | Count | Status |
|---|---|---|
| Existing MathComp (Chapter 1) | 17 definitions/lemmas | `\rocqok` (pre-existing) |
| New carry arithmetic (Chapter 2) | 8 definitions/lemmas | ✅ **8/8 `\rocqok`** |
| New Legendre connection (Chapter 3) | 4 lemmas | 0/4 |
| New Kummer theorem (Chapter 4) | 2 theorems | 0/2 |
| New corollaries (Chapter 5) | 6 lemmas | 0/6 |
| New digit sums (Chapter 6, optional) | 6 definitions/lemmas/theorems | 0/6 |
| **Total new nodes** | **26** | **8/26 proven** |
| **Total blueprint nodes** | **43** | **25/43 `\rocqok`** |
