import Proof

/-!
# JSP-000243 — the challenge, precisely stated, and the answer

> **Catalog text.** *What is the shortest integer interval containing distinct
> denominators whose reciprocals sum to one?*

This file turns that sentence into a definition and then states the answer as a
theorem.  All mathematical content is proved in `Proof.lean`; nothing here is
`sorry`-ed.

## Reading the encoding

For a starting point `a ≥ 2` we look at the window of five consecutive integers

    a, a + 1, a + 2, a + 3, a + 4

and a subset of it, encoded by five Booleans `b₀ … b₄` (`bᵢ = true` means
`a + i` is one of the denominators).  `Jsp000243.selSum a ha b₀ b₁ b₂ b₃ b₄`
is the rational number `Σ 1/(a+i)` over the selected `i`, as a concrete
fraction (`Jsp000243.Frac`), and `Jsp000243.Frac.eqv` is equality of rationals
by cross multiplication.  The five Booleans range over **all 32 subsets** of the
window, so no subset is missed.

An interval `[a, a+d]` of *width* (diameter) `d` contains the selected
denominators exactly when selecting `a+i` forces `i ≤ d`; that is the family of
implications in `Admits` below.  Windows of width `≤ 3` are therefore covered
by the same encoding with `b₄ = false`.
-/

open Jsp000243

/-- `Admits a d ha` says: the integer interval `[a, a + d]`, with `a ≥ 2`,
contains a **nonempty** set of **distinct** integers whose reciprocals sum to
`1`.

Distinctness is automatic — the five Booleans select each of
`a, a+1, a+2, a+3, a+4` at most once.  Containment in `[a, a+d]` is expressed
by the four implications `bᵢ = true → i ≤ d`.  Only widths `d ≤ 4` are needed
for JSP-000243, so a five-wide window suffices. -/
def Admits (a d : Nat) (ha : 2 ≤ a) : Prop :=
  ∃ b0 b1 b2 b3 b4 : Bool,
    (b0 = true ∨ b1 = true ∨ b2 = true ∨ b3 = true ∨ b4 = true) ∧
    (b1 = true → 1 ≤ d) ∧ (b2 = true → 2 ≤ d) ∧
    (b3 = true → 3 ≤ d) ∧ (b4 = true → 4 ≤ d) ∧
    Frac.eqv (selSum a ha b0 b1 b2 b3 b4) Frac.one

/-- **No interval of width `≤ 3` works**, whatever its starting point `a ≥ 2`. -/
theorem no_admits_width_three (a d : Nat) (ha : 2 ≤ a) (hd : d ≤ 3) :
    ¬ Admits a d ha := by
  intro h
  obtain ⟨b0, b1, b2, b3, b4, _hne, _h1, _h2, _h3, h4, hsum⟩ := h
  cases b4 with
  | false => exact no_diameter_three a ha b0 b1 b2 b3 hsum
  | true => exact absurd (h4 rfl) (by omega)

/-- **Width `4` does work**: `[2, 6]` contains `{2, 3, 6}` and
`1/2 + 1/3 + 1/6 = 1`. -/
theorem admits_width_four : Admits 2 4 two_le_two :=
  ⟨true, true, false, false, true,
   by decide, by decide, by decide, by decide, by decide,
   two_six_works⟩

/-- **Answer to JSP-000243.**

The shortest integer interval containing distinct denominators whose
reciprocals sum to one has width (diameter) **exactly `4`**, i.e. it consists
of **five** consecutive integers:

* some interval of width `4` works — `[2, 6]` (`admits_width_four`);
* no interval of width `≤ 3` works, for any starting point `a ≥ 2`
  (`no_admits_width_three`).

Combined with `Jsp000243.no_diameter_four_ge_three` (no width-`4` interval
works unless it starts at `a = 2`) and `Jsp000243.unique_subset_of_two_six`
(inside `[2, 6]`, `{2, 3, 6}` is the unique choice), the answer is completely
determined:

> the shortest such interval is **`[2, 6]`**, and the denominators are
> uniquely **`{2, 3, 6}`**, since `1/2 + 1/3 + 1/6 = 1`. -/
theorem shortest_width_is_four :
    (∃ (a : Nat) (ha : 2 ≤ a), Admits a 4 ha) ∧
    (∀ (a : Nat) (ha : 2 ≤ a) (d : Nat), d ≤ 3 → ¬ Admits a d ha) :=
  ⟨⟨2, two_le_two, admits_width_four⟩,
   fun a ha d hd => no_admits_width_three a d ha hd⟩

/-- **The optimal interval is unique.**  `[2, 6]` is the only width-`4` interval
that works: for `a ≥ 3` no subset of `{a, …, a+4}` has reciprocals summing
to `1`. -/
theorem unique_optimal_interval :
    (∀ (a : Nat) (ha : 2 ≤ a) (h3 : 3 ≤ a), ¬ Admits a 4 ha) ∧ Admits 2 4 two_le_two :=
  ⟨fun a ha h3 h => by
     obtain ⟨b0, b1, b2, b3, b4, _hne, _h1, _h2, _h3, _h4, hsum⟩ := h
     exact no_diameter_four_ge_three a ha h3 b0 b1 b2 b3 b4 hsum,
   admits_width_four⟩

/-- **The optimal representation is unique.**  Among all 32 subsets of
`{2, 3, 4, 5, 6}`, exactly one has reciprocals summing to `1`: `{2, 3, 6}`. -/
theorem unique_optimal_representation (b0 b1 b2 b3 b4 : Bool) :
    Frac.eqv (selSum 2 two_le_two b0 b1 b2 b3 b4) Frac.one
      ↔ b0 = true ∧ b1 = true ∧ b2 = false ∧ b3 = false ∧ b4 = true :=
  unique_subset_of_two_six b0 b1 b2 b3 b4
