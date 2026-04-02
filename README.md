# Kummer's theorem in MathComp

A formalization of [Kummer's theorem](https://en.wikipedia.org/wiki/Kummer%27s_theorem) in the [MathComp](https://math-comp.github.io/) library, with a [rocqblueprint](https://github.com/PatrickMassot/rocqblueprint)-powered dependency graph tracking formalization progress.

**Kummer's theorem** states that the p-adic valuation of the binomial coefficient C(n, k) equals the number of carries when adding k and n−k in base p.

## Project structure

```
mathcomp-kummer/
├── theories/
│   ├── divn_carry.v        # Floor-division addition identity, carry predicate
│   ├── logn_bin.v          # Legendre connection + Kummer's theorem
│   ├── logn_bin_extra.v    # Corollaries (upper bounds, special cases)
│   └── digit_sum.v         # Digit sums, alternative Kummer formulation
├── blueprint/
│   └── src/                # LaTeX blueprint with dependency annotations
├── _CoqProject
└── Makefile
```

## Prerequisites

- [opam](https://opam.ocaml.org/) with a Rocq/Coq switch
- [MathComp](https://github.com/math-comp/math-comp) (ssreflect, boot, order)
- Python 3 with [uv](https://github.com/astral-sh/uv) (for the blueprint)

## Building the Rocq project

```bash
make
```

## Viewing the blueprint

Install the blueprint tooling (once):

```bash
uv venv
source .venv/bin/activate
CFLAGS="-I$(brew --prefix graphviz)/include" \
LDFLAGS="-L$(brew --prefix graphviz)/lib" \
uv pip install rocqblueprint
```

Build and serve the blueprint:

```bash
source .venv/bin/activate
python3 blueprint/update_status.py   # sync proof status from .v files
cd blueprint/src
rocqblueprint web
cd web && python3 -m http.server 8080
```

Then open locally:

- **Blueprint**: http://localhost:8080/index.html
- **Dependency graph**: http://localhost:8080/dep_graph_document.html

The blueprint is also deployed at: https://llm4rocq.github.io/mathcomp-kummer/

> The dependency graph requires a local HTTP server because it uses WebAssembly (`.wasm` files), which browsers block when opened via `file://`.

## Formalization plan

The proof follows the chain:

1. **Carry arithmetic** (`divn_carry.v`): prove the floor-division addition identity `(a+b)/m = a/m + b/m + [m <= a%%m + b%%m]`, then sum it over powers of p.
2. **Legendre connection** (`logn_bin.v`): express `logn p C(n,k)` as a difference of Legendre sums using `bin_fact` and `lognM`.
3. **Kummer's theorem** (`logn_bin.v`): combine steps 1 and 2.
4. **Corollaries** (`logn_bin_extra.v`): upper bounds, vanishing results, prime power cases.
5. **Digit sums** (`digit_sum.v`): alternative formulation via `(p-1) * logn p C(n,k) = s_p(k) + s_p(n-k) - s_p(n)`.

