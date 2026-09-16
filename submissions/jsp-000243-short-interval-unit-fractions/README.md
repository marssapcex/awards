# JSP-000243 · What is the shortest integer interval containing distinct denominators whose reciprocals sum to one?

**Status of this submission:** a complete formal proof, in Lean 4, of the exact
answer to the question as it is posed in the
[catalog](../../problems/catalog-0201-0300.md#JSP-000243).

| field | value |
| --- | --- |
| Problem | [JSP-000243](../../problems/catalog-0201-0300.md#JSP-000243) |
| Area | Number theory / unit fractions |
| Catalog status before this submission | Solved (`[Cr01]` Craven, *Acta Arith.* **99** (2001), 99–114), Lean **No**, Eligible **No**, Claim **Unavailable** |
| Answer proved here | width (diameter) **4** — five consecutive integers — uniquely `[2, 6]`, uniquely `{2, 3, 6}` |
| Dependencies | **core Lean 4 only**; no Mathlib |
| Axioms used | `[propext, Quot.sound]` (and `[propext]` for most lemmas) — strictly below the `[propext, Classical.choice, Quot.sound]` baseline |
| Holes | none: no `sorry`, no `admit`, no `native_decide`, no user-declared `axiom` |
| Toolchain | `leanprover/lean4:v4.34.0` (latest stable release) |
| Recipient | `RECIPIENT-JSP-000243-A` (placeholder; confirmation pending) |

---

## 1. The problem

> What is the shortest integer interval containing distinct denominators whose
> reciprocals sum to one?

Read literally this is a **finite** question, and it has an exact answer.
Two conventions are forced by the wording and are made explicit here:

* **Denominators are at least `2`.** This is the standard convention for unit
  (Egyptian) fractions. Without it the question is vacuous, since `[1, 1]`
  already contains `{1}` and `1/1 = 1`.
* **The "length" of an interval `[a, b]` is its width `b − a`** (so `[2, 6]`
  has width `4` and contains `5` integers). Both readings are settled below:
  width `4`, equivalently five consecutive integers.

Formally: call `d` *admissible* if there are `a ≥ 2` and distinct integers
`k₁, …, k_m ⊆ [a, a+d]` with `Σ 1/kᵢ = 1`. The question asks for `min d`.

## 2. The answer, and what is proved

**The minimum is `d = 4`, attained only by `[2, 6]`, only by `{2, 3, 6}`:**

$$\frac12+\frac13+\frac16=1,\qquad \{2,3,6\}\subseteq[2,6].$$

| theorem (in `Challenge.lean` / `Proof.lean`) | statement |
| --- | --- |
| `admits_width_four` | `[2, 6]` contains distinct denominators whose reciprocals sum to `1` |
| `no_admits_width_three` | for every `a ≥ 2` and every `d ≤ 3`, `[a, a+d]` contains **no** such set |
| `shortest_width_is_four` | the two above, combined: the minimum width is exactly `4` |
| `no_diameter_four_ge_three` | for every `a ≥ 3`, **no** subset of `{a,…,a+4}` sums to `1` — so the width-`4` interval is unique |
| `unique_optimal_interval` | `[2, 6]` is the only width-`4` interval that works |
| `unique_subset_of_two_six` / `unique_optimal_representation` | among all `32` subsets of `{2,3,4,5,6}`, `{2,3,6}` is the **only** one whose reciprocals sum to `1` |
| `no_diameter_three` | the underlying width-`≤3` impossibility, for all `a ≥ 2` |
| `sums_to_one_iff` | the clearing bridge: the *rational* equation `Σ 1/k = 1` is equivalent to the *natural-number* equation `cleared a b = D5 a` (machine-checked, not asserted) |

## 3. Proof strategy

Rational numbers are modelled concretely, so that nothing outside core Lean is
needed:

```lean
structure Frac where n : Nat; d : Nat; dpos : 0 < d
def Frac.eqv (x y : Frac) : Prop := x.n * y.d = y.n * x.d
```

`Frac.eqv` is proved to be an equivalence (`Frac.eqv_trans` uses
`Nat.eq_of_mul_eq_mul_right`), addition is `Frac.add`, and
`Frac.eq_one_iff` says `n/d = 1 ↔ n = d`.

For a start `a` and the five-wide window `a, …, a+4` put

```
D5 a = a·(a+1)·(a+2)·(a+3)·(a+4)
q0 a = D5 a / a       = (a+1)(a+2)(a+3)(a+4)
q1 a = D5 a / (a+1)   = a(a+2)(a+3)(a+4)
q2 a = D5 a / (a+2)   = a(a+1)(a+3)(a+4)
q3 a = D5 a / (a+3)   = a(a+1)(a+2)(a+4)
q4 a = D5 a / (a+4)   = a(a+1)(a+2)(a+3)
```

A subset of the window is a 5-tuple of Booleans `b₀…b₄`; `selSum a ha b` is the
rational `Σ 1/(a+i)` over the selected `i`, and

```
cleared a b = Σᵢ (if bᵢ then qᵢ a else 0) = D5 a · Σ 1/(a+i).
```

The five identities `mul_q0 … mul_q4` — `(a+i)·qᵢ a = D5 a` — are exactly the
statement that `D5 a` is a common multiple of the window, and they are what make
`selSum_eqv_cleared` and then `sums_to_one_iff` go through:

> `Σ 1/(a+i) = 1` (in `ℚ`) **iff** `cleared a b = D5 a` (in `ℕ`).

So the whole problem becomes one inequality about natural numbers, and it splits
in two:

* **`a ∈ {3,4,5}`** — exhaustive: `3 × 32 = 96` closed goals, each discharged by
  `decide`.
* **`a ≥ 6`** — an estimate. Each `qᵢ a ≤ q0 a` (`q1_le_q0 … q4_le_q0`, each a
  one- or two-step monotonicity of multiplication, since every factor of `qᵢ` is
  at most the corresponding factor of `q0`). Hence
  `cleared a b ≤ 5·q0 a`, while `5·q0 a < a·q0 a = D5 a` because `5 < a` and
  `q0 a > 0`. So `cleared a b < D5 a` and equality is impossible.

The start `a = 2` is again exhaustive (`32` goals, `decide`); it simultaneously
produces the witness `{2,3,6}` and its uniqueness inside `[2,6]`.

Widths `≤ 3` need no separate argument: a subset of `[a, a+d]` with `d ≤ 3` is a
subset of `{a,…,a+4}` with `b₄ = false`, which is already excluded.

## 4. Scope — what this submission does **not** claim

This is stated explicitly so that the record is not over-read.

* The catalog entry for JSP-000243 is marked *Solved* with reference `[Cr01]`,
  Craven, *On unit fractions with denominators in short intervals*,
  *Acta Arithmetica* **99** (2001), 99–114. That paper concerns the
  **asymptotic** theory of unit fractions with denominators in short intervals
  (which intervals of given relative length admit such representations as the
  start point grows). **Nothing in that asymptotic theory is formalised or
  claimed here.**
* What is proved here is the **literal question in the catalog description** —
  a finite extremal question — and it is answered completely and exactly.
* Consequently this submission should be read as *supplying the missing Lean
  formalisation of the finite question posed by JSP-000243*, not as a new
  result in the asymptotic direction, and not as a verification of Craven's
  paper.

Supporting (computer-verified but **not** machine-checked) data, obtained by
exact rational enumeration, for the minimal width `L(a)` as a function of the
start point `a` — consistent with the theorems above and included only as
context:

| `a` | 2 | 3 | 4 | 5 | 6 | 7 |
| --- | --- | --- | --- | --- | --- | --- |
| minimal width `L(a)` | 4 | 12 | 16 | 19 | 22 | 26 |

## 5. Reproducing the check

With a normal `elan`/`lake` installation:

```console
$ lake build
```

This compiles `Proof.lean` (which has no `import` line and therefore
auto-imports `Init`), `Challenge.lean` and `Audit.lean`, and prints the axiom
audit. Expected result: no errors, and every printed dependency is a subset of
`[propext, Quot.sound]`.

[`verification.txt`](verification.txt) records the check actually performed for
this submission, including SHA-256 digests and byte counts of every file, the
verbatim `#print axioms` output, and a full disclosure of the environment
constraints under which it was produced (no Lean release host was reachable, so
the 4.35.0 compiler and its core library had to be built from source; see
§4 of that file for exactly how the check was set up and why it is equivalent to
`lake build` for the submitted body).

## 6. Files

| file | contents |
| --- | --- |
| [`Proof.lean`](Proof.lean) | the mathematical development: the `Frac` model, the five exact-division identities, the clearing bridge, the estimate for `a ≥ 6`, the exhaustive cases, and the four main theorems |
| [`Challenge.lean`](Challenge.lean) | the catalog question turned into a definition (`Admits`) and the answer turned into theorems (`shortest_width_is_four`, `unique_optimal_interval`, `unique_optimal_representation`) |
| [`Audit.lean`](Audit.lean) | `#print axioms` for every top-level result |
| [`lakefile.toml`](lakefile.toml), [`lean-toolchain`](lean-toolchain), [`lake-manifest.json`](lake-manifest.json) | build configuration; no dependencies |
| [`STATEMENT.md`](STATEMENT.md) | statement-fidelity cross-reference: conventions, claim-by-claim mapping to Lean names, and explicit non-claims |
| [`verification.txt`](verification.txt) | digests, verbatim kernel output, and full provenance disclosure |
| [`SHA256SUMS`](SHA256SUMS) | `sha256sum -c` digest list for every file in this directory |
| [`verification/crosscheck.py`](verification/crosscheck.py) | independent exact-rational cross-check; runs in under a second, needs no Lean |

## 7. Provenance and disclosure

* **Self-submission.** This submission is offered by its own author; no
  maintainer or committee member is involved.
* **AI assistance.** This formalisation was prepared **with AI assistance**,
  under the direction of the submitting account. The authority relied on is the
  Lean 4 kernel check recorded in `verification.txt`, not the assistant; the
  independent exact-rational enumeration in
  `verification/crosscheck.py` is provided so that a reviewer can re-derive the
  same facts without Lean at all.
* **Conflict of interest.** None known.
* **Recipient.** `RECIPIENT-JSP-000243-A` (placeholder; confirmation pending).
  No identity is asserted or published.
* **No reuse of third-party code.** No part of any other formalisation, and no
  part of Mathlib, is used: `Proof.lean` has no `import` line at all and
  therefore depends only on the Lean 4 core library.
* **License.** MIT, matching the repository's [LICENSE](../../LICENSE).
