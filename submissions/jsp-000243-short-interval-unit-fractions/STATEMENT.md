# JSP-000243 — statement fidelity

This file exists so that a reviewer can check, line by line, that the Lean
theorems say what the catalog question asks. Nothing here is proved; it is a
cross-reference. Proofs are in [`Proof.lean`](Proof.lean) and
[`Challenge.lean`](Challenge.lean).

## 1. The catalog text

> **JSP-000243.** *What is the shortest integer interval containing distinct
> denominators whose reciprocals sum to one?*
>
> Area: Number theory / Unit fractions. Status: Solved. Lean: No.
> Eligible to claim: No. Claim: Unavailable.
> Publication: `[Cr01]` *On unit fractions with denominators in short
> intervals*, Acta Arith. **99** (2001), 99–114.

## 2. Conventions needed to make the question precise

The catalog sentence is finite but leaves two conventions implicit. Both are
fixed explicitly here, and both are the standard reading.

| convention | choice | why it is forced |
| --- | --- | --- |
| denominators | integers `≥ 2` | standard for unit / Egyptian fractions. If `1` were allowed the question is vacuous: `[1,1]` contains `{1}` and `1/1 = 1`, so the answer would be `0`. |
| "shortest interval" | the **width** `b − a` of `[a, b]` | this is the only reading under which the answer is a single number. The equivalent count of integers is `width + 1`, and both are reported below. |
| "distinct denominators" | a **subset** of the interval | each integer of the interval may be used at most once; encoded by one Boolean per integer, so no multiset/repetition reading is possible. |
| "containing" | the denominators lie **inside** `[a, b]` | they need not include the endpoints. |

## 3. What is claimed

**Answer.** The minimum width is **4** — five consecutive integers. The
interval is **unique**: `[2, 6]`. The denominators are **unique** inside it:
`{2, 3, 6}`, because `1/2 + 1/3 + 1/6 = 1`.

| # | natural-language claim | Lean name | file |
| --- | --- | --- | --- |
| 1 | `[2,6]` contains a nonempty set of distinct integers `≥2` whose reciprocals sum to `1` | `admits_width_four` | Challenge.lean |
| 2 | for every `a ≥ 2` and every `d ≤ 3`, `[a, a+d]` contains **no** such set | `no_admits_width_three` | Challenge.lean |
| 3 | therefore the minimum width is exactly `4` | `shortest_width_is_four` | Challenge.lean |
| 4 | for every `a ≥ 3`, `[a, a+4]` contains no such set — so `[2,6]` is the **only** width-`4` interval | `unique_optimal_interval` | Challenge.lean |
| 5 | among all `32` subsets of `{2,3,4,5,6}`, `{2,3,6}` is the **only** one whose reciprocals sum to `1` | `unique_optimal_representation` | Challenge.lean |
| 6 | for every `a ≥ 2` and every subset of `{a, a+1, a+2, a+3}`, the reciprocals do **not** sum to `1` | `no_diameter_three` | Proof.lean |
| 7 | for every `a ≥ 3` and every subset of `{a, …, a+4}`, the reciprocals do **not** sum to `1` | `no_diameter_four_ge_three` | Proof.lean |
| 8 | `1/2 + 1/3 + 1/6 = 1`, as an equality of the concrete rational model | `two_six_works` | Proof.lean |
| 9 | the *rational* equation `Σ 1/k = 1` is equivalent to the *natural-number* equation `cleared a b = D5 a` | `sums_to_one_iff` | Proof.lean |
| 10 | `D5 a = a(a+1)(a+2)(a+3)(a+4)` really is a common multiple of the window | `mul_q0 … mul_q4` | Proof.lean |

Claim 9 is the one that makes the rest faithful rather than merely
arithmetic-shaped: it is proved, not asserted, so the theorems are genuinely
about sums of reciprocals of rationals and not only about an integer equation.

## 4. Encoding of "subset of an interval"

For a start `a` the window `a, a+1, a+2, a+3, a+4` is fixed, and a subset is a
5-tuple of Booleans `b₀ … b₄` (`bᵢ = true` ⟺ `a+i` is one of the
denominators). `Jsp000243.selSum a ha b₀ b₁ b₂ b₃ b₄` is the rational
`Σ 1/(a+i)` over the selected `i`.

The five Booleans range over **all 32 subsets**, so nothing is missed. An
interval `[a, a+d]` with `d ≤ 4` contains the selected denominators exactly when
selecting `a+i` forces `i ≤ d`; that is the family of implications in the
definition of `Admits` in `Challenge.lean`. Widths `d ≤ 3` are therefore the
same statement with `b₄ = false`, which is why no separate argument is needed
for them.

## 5. Scope — what is **not** claimed

* `[Cr01]` (Craven, *Acta Arith.* 2001) concerns the **asymptotic** theory of
  unit fractions with denominators in short intervals. **No part of that
  asymptotic theory is formalised, reproved, or claimed here.**
* What is proved is the **finite extremal question exactly as the catalog
  description poses it**, answered completely: minimum width, uniqueness of the
  interval, uniqueness of the denominator set.
* No new mathematics is claimed: the answer `1/2 + 1/3 + 1/6 = 1` and the
  impossibility for shorter intervals are elementary and long known. The
  contribution is the **machine-checked formalisation**, which is precisely the
  field (`Lean = No`) that currently makes this record `Eligible to claim = No`.
* The table of minimal widths `L(a)` for `a = 3 … 7` in
  [`README.md`](README.md) §4 is **computer-verified but not machine-checked**;
  it is context only, and no theorem in this submission depends on it.
