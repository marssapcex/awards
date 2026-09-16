/-
Copyright (c) 2026 JSP-000243 submission authors.
Released under the MIT license (see LICENSE at the repository root).

# JSP-000243 · What is the shortest integer interval containing distinct
               denominators whose reciprocals sum to one?

This file is a complete, self-contained formal proof in **core Lean 4** —
it uses no Mathlib and no axioms beyond `propext` and `Quot.sound`
(it does not even use `Classical.choice`).  There is no `sorry`, no `admit`,
no `native_decide` and no user-declared `axiom` anywhere in the file.

The file has no `import` line, so Lean automatically imports `Init`;
everything used (`Nat` arithmetic, `omega`, `decide`, `simp only`, `rcases`)
is part of the Lean 4 core library.
-/

namespace Jsp000243

/-! ## 1. A concrete model of the non-negative rationals -/

/-- `Frac.mk n d hd` denotes the rational number `n / d` (`d > 0`).
This is all of the theory of `ℚ≥0` that JSP-000243 needs, and it keeps the
development inside core Lean (no Mathlib). -/
structure Frac where
  /-- numerator -/
  n : Nat
  /-- denominator -/
  d : Nat
  /-- the denominator is positive -/
  dpos : 0 < d

/-- Two concrete fractions denote the same rational number iff their cross
products agree. -/
def Frac.eqv (x y : Frac) : Prop := x.n * y.d = y.n * x.d

theorem Frac.eqv_refl (x : Frac) : x.eqv x := rfl

theorem Frac.eqv_symm {x y : Frac} (h : x.eqv y) : y.eqv x := h.symm

theorem Frac.eqv_trans {x y z : Frac} (hxy : x.eqv y) (hyz : y.eqv z) : x.eqv z :=
  Nat.eq_of_mul_eq_mul_right y.dpos <| by
    calc (x.n * z.d) * y.d
        = x.n * (z.d * y.d) := by rw [Nat.mul_assoc]
      _ = x.n * (y.d * z.d) := by rw [Nat.mul_comm z.d y.d]
      _ = (x.n * y.d) * z.d := by rw [← Nat.mul_assoc]
      _ = (y.n * x.d) * z.d := by rw [hxy]
      _ = y.n * (x.d * z.d) := by rw [Nat.mul_assoc]
      _ = y.n * (z.d * x.d) := by rw [Nat.mul_comm x.d z.d]
      _ = (y.n * z.d) * x.d := by rw [← Nat.mul_assoc]
      _ = (z.n * y.d) * x.d := by rw [hyz]
      _ = z.n * (y.d * x.d) := by rw [Nat.mul_assoc]
      _ = z.n * (x.d * y.d) := by rw [Nat.mul_comm y.d x.d]
      _ = (z.n * x.d) * y.d := by rw [← Nat.mul_assoc]

/-- The rational number `0`. -/
def Frac.zero : Frac := ⟨0, 1, Nat.succ_pos 0⟩

/-- The rational number `1`. -/
def Frac.one : Frac := ⟨1, 1, Nat.succ_pos 0⟩

/-- The rational number `1 / k`. -/
def Frac.recip (k : Nat) (hk : 0 < k) : Frac := ⟨1, k, hk⟩

/-- Addition of concrete fractions. -/
def Frac.add (x y : Frac) : Frac :=
  ⟨x.n * y.d + y.n * x.d, x.d * y.d, Nat.mul_pos x.dpos y.dpos⟩

theorem Frac.eq_one_iff {n d : Nat} (hd : 0 < d) :
    Frac.eqv ⟨n, d, hd⟩ Frac.one ↔ n = d := by
  constructor
  · intro h
    have h' : n * 1 = 1 * d := h
    rw [Nat.mul_one, Nat.one_mul] at h'
    exact h'
  · intro h
    have g : n * 1 = 1 * d := by rw [h, Nat.mul_one, Nat.one_mul]
    exact g

theorem Frac.zero_eqv {d : Nat} (hd : 0 < d) : Frac.eqv Frac.zero ⟨0, d, hd⟩ := by
  show 0 * d = 0 * 1
  rw [Nat.zero_mul, Nat.zero_mul]

theorem Frac.add_same_den {n1 n2 d : Nat} (hd : 0 < d) :
    Frac.eqv (Frac.add ⟨n1, d, hd⟩ ⟨n2, d, hd⟩) ⟨n1 + n2, d, hd⟩ := by
  show (n1 * d + n2 * d) * d = (n1 + n2) * (d * d)
  rw [Nat.add_mul, Nat.add_mul, ← Nat.mul_assoc, ← Nat.mul_assoc]

theorem Frac.add_eqv {x x' y y' : Frac} (hx : Frac.eqv x x') (hy : Frac.eqv y y') :
    Frac.eqv (Frac.add x y) (Frac.add x' y') := by
  have h1 : (x.n * y.d) * (x'.d * y'.d) = (x'.n * y'.d) * (x.d * y.d) := by
    have s1 : (x.n * y.d) * (x'.d * y'.d) = (x.n * x'.d) * (y.d * y'.d) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have s2 : (x'.n * x.d) * (y.d * y'.d) = (x'.n * y'.d) * (x.d * y.d) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [s1, hx, s2]
  have h2 : (y.n * x.d) * (x'.d * y'.d) = (y'.n * x'.d) * (x.d * y.d) := by
    have s1 : (y.n * x.d) * (x'.d * y'.d) = (y.n * y'.d) * (x.d * x'.d) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have s2 : (y'.n * y.d) * (x.d * x'.d) = (y'.n * x'.d) * (x.d * y.d) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [s1, hy, s2]
  show (x.n * y.d + y.n * x.d) * (x'.d * y'.d) =
       (x'.n * y'.d + y'.n * x'.d) * (x.d * y.d)
  rw [Nat.add_mul, Nat.add_mul, h1, h2]

/-- Adding two fractions that are both already presented over the common
denominator `d`. -/
theorem Frac.add_common {d : Nat} (hd : 0 < d) {x y : Frac} {n1 n2 : Nat}
    (hx : Frac.eqv x ⟨n1, d, hd⟩) (hy : Frac.eqv y ⟨n2, d, hd⟩) :
    Frac.eqv (Frac.add x y) ⟨n1 + n2, d, hd⟩ :=
  Frac.eqv_trans (Frac.add_eqv hx hy) (Frac.add_same_den hd)

/-! ## 2. Five consecutive denominators and their common multiple -/

/-- `D5 a = a * (a+1) * (a+2) * (a+3) * (a+4)`: a common multiple of the five
consecutive candidate denominators starting at `a`. -/
def D5 (a : Nat) : Nat := a * (a + 1) * (a + 2) * (a + 3) * (a + 4)

/-- `D5 a / a` -/
def q0 (a : Nat) : Nat := (a + 1) * (a + 2) * (a + 3) * (a + 4)
/-- `D5 a / (a+1)` -/
def q1 (a : Nat) : Nat := a * (a + 2) * (a + 3) * (a + 4)
/-- `D5 a / (a+2)` -/
def q2 (a : Nat) : Nat := a * (a + 1) * (a + 3) * (a + 4)
/-- `D5 a / (a+3)` -/
def q3 (a : Nat) : Nat := a * (a + 1) * (a + 2) * (a + 4)
/-- `D5 a / (a+4)` -/
def q4 (a : Nat) : Nat := a * (a + 1) * (a + 2) * (a + 3)

theorem pos_a (a : Nat) (ha : 2 ≤ a) : 0 < a := Nat.lt_of_lt_of_le (Nat.succ_pos 1) ha
theorem pos_a1 (a : Nat) : 0 < a + 1 := Nat.succ_pos a
theorem pos_a2 (a : Nat) : 0 < a + 2 := Nat.succ_pos (a + 1)
theorem pos_a3 (a : Nat) : 0 < a + 3 := Nat.succ_pos (a + 2)
theorem pos_a4 (a : Nat) : 0 < a + 4 := Nat.succ_pos (a + 3)

theorem D5pos (a : Nat) (ha : 2 ≤ a) : 0 < D5 a := by
  show 0 < ((a * (a + 1)) * (a + 2) * (a + 3)) * (a + 4)
  exact Nat.mul_pos
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pos_a a ha) (pos_a1 a)) (pos_a2 a)) (pos_a3 a))
    (pos_a4 a)

/-- The five exact-division identities: `D5 a` really is a common multiple. -/
theorem mul_q0 (a : Nat) : a * q0 a = D5 a := by
  show a * ((a + 1) * (a + 2) * (a + 3) * (a + 4)) = a * (a + 1) * (a + 2) * (a + 3) * (a + 4)
  rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc]

theorem mul_q1 (a : Nat) : (a + 1) * q1 a = D5 a := by
  show (a + 1) * (a * (a + 2) * (a + 3) * (a + 4)) = a * (a + 1) * (a + 2) * (a + 3) * (a + 4)
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem mul_q2 (a : Nat) : (a + 2) * q2 a = D5 a := by
  show (a + 2) * (a * (a + 1) * (a + 3) * (a + 4)) = a * (a + 1) * (a + 2) * (a + 3) * (a + 4)
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem mul_q3 (a : Nat) : (a + 3) * q3 a = D5 a := by
  show (a + 3) * (a * (a + 1) * (a + 2) * (a + 4)) = a * (a + 1) * (a + 2) * (a + 3) * (a + 4)
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem mul_q4 (a : Nat) : (a + 4) * q4 a = D5 a := by
  show (a + 4) * (a * (a + 1) * (a + 2) * (a + 3)) = a * (a + 1) * (a + 2) * (a + 3) * (a + 4)
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-! ## 3. Subsets of the window, as rational numbers and as cleared naturals -/

/-- The sum of the reciprocals of the selected members of
`{a, a+1, a+2, a+3, a+4}`, as a concrete rational number.  The five Booleans
range over **all** 32 subsets of the window. -/
def selSum (a : Nat) (ha : 2 ≤ a) (b0 b1 b2 b3 b4 : Bool) : Frac :=
  Frac.add (if b0 then Frac.recip a (pos_a a ha) else Frac.zero)
    (Frac.add (if b1 then Frac.recip (a + 1) (pos_a1 a) else Frac.zero)
      (Frac.add (if b2 then Frac.recip (a + 2) (pos_a2 a) else Frac.zero)
        (Frac.add (if b3 then Frac.recip (a + 3) (pos_a3 a) else Frac.zero)
                  (if b4 then Frac.recip (a + 4) (pos_a4 a) else Frac.zero))))

/-- `D5 a * Σ (1/k)` over the selected members of the window: an exact natural
number, because each `a+i` divides `D5 a`. -/
def cleared (a : Nat) (b0 b1 b2 b3 b4 : Bool) : Nat :=
  (if b0 then q0 a else 0)
    + ((if b1 then q1 a else 0)
      + ((if b2 then q2 a else 0)
        + ((if b3 then q3 a else 0) + (if b4 then q4 a else 0))))

theorem t0_eqv (a : Nat) (ha : 2 ≤ a) (b : Bool) :
    Frac.eqv (if b then Frac.recip a (pos_a a ha) else Frac.zero)
      ⟨if b then q0 a else 0, D5 a, D5pos a ha⟩ := by
  cases b
  · exact Frac.zero_eqv (D5pos a ha)
  · show 1 * D5 a = q0 a * a
    rw [Nat.one_mul, Nat.mul_comm, mul_q0]

theorem t1_eqv (a : Nat) (ha : 2 ≤ a) (b : Bool) :
    Frac.eqv (if b then Frac.recip (a + 1) (pos_a1 a) else Frac.zero)
      ⟨if b then q1 a else 0, D5 a, D5pos a ha⟩ := by
  cases b
  · exact Frac.zero_eqv (D5pos a ha)
  · show 1 * D5 a = q1 a * (a + 1)
    rw [Nat.one_mul, Nat.mul_comm, mul_q1]

theorem t2_eqv (a : Nat) (ha : 2 ≤ a) (b : Bool) :
    Frac.eqv (if b then Frac.recip (a + 2) (pos_a2 a) else Frac.zero)
      ⟨if b then q2 a else 0, D5 a, D5pos a ha⟩ := by
  cases b
  · exact Frac.zero_eqv (D5pos a ha)
  · show 1 * D5 a = q2 a * (a + 2)
    rw [Nat.one_mul, Nat.mul_comm, mul_q2]

theorem t3_eqv (a : Nat) (ha : 2 ≤ a) (b : Bool) :
    Frac.eqv (if b then Frac.recip (a + 3) (pos_a3 a) else Frac.zero)
      ⟨if b then q3 a else 0, D5 a, D5pos a ha⟩ := by
  cases b
  · exact Frac.zero_eqv (D5pos a ha)
  · show 1 * D5 a = q3 a * (a + 3)
    rw [Nat.one_mul, Nat.mul_comm, mul_q3]

theorem t4_eqv (a : Nat) (ha : 2 ≤ a) (b : Bool) :
    Frac.eqv (if b then Frac.recip (a + 4) (pos_a4 a) else Frac.zero)
      ⟨if b then q4 a else 0, D5 a, D5pos a ha⟩ := by
  cases b
  · exact Frac.zero_eqv (D5pos a ha)
  · show 1 * D5 a = q4 a * (a + 4)
    rw [Nat.one_mul, Nat.mul_comm, mul_q4]

/-- **Faithfulness of the clearing step.**  The rational number
`selSum a ha b₀ b₁ b₂ b₃ b₄` is exactly `cleared a b / D5 a`. -/
theorem selSum_eqv_cleared (a : Nat) (ha : 2 ≤ a) (b0 b1 b2 b3 b4 : Bool) :
    Frac.eqv (selSum a ha b0 b1 b2 b3 b4)
      ⟨cleared a b0 b1 b2 b3 b4, D5 a, D5pos a ha⟩ := by
  have h34 : Frac.eqv
      (Frac.add (if b3 then Frac.recip (a + 3) (pos_a3 a) else Frac.zero)
                (if b4 then Frac.recip (a + 4) (pos_a4 a) else Frac.zero))
      ⟨(if b3 then q3 a else 0) + (if b4 then q4 a else 0), D5 a, D5pos a ha⟩ :=
    Frac.add_common (D5pos a ha) (t3_eqv a ha b3) (t4_eqv a ha b4)
  have h234 : Frac.eqv
      (Frac.add (if b2 then Frac.recip (a + 2) (pos_a2 a) else Frac.zero)
        (Frac.add (if b3 then Frac.recip (a + 3) (pos_a3 a) else Frac.zero)
                  (if b4 then Frac.recip (a + 4) (pos_a4 a) else Frac.zero)))
      ⟨(if b2 then q2 a else 0) + ((if b3 then q3 a else 0) + (if b4 then q4 a else 0)),
        D5 a, D5pos a ha⟩ :=
    Frac.add_common (D5pos a ha) (t2_eqv a ha b2) h34
  have h1234 : Frac.eqv
      (Frac.add (if b1 then Frac.recip (a + 1) (pos_a1 a) else Frac.zero)
        (Frac.add (if b2 then Frac.recip (a + 2) (pos_a2 a) else Frac.zero)
          (Frac.add (if b3 then Frac.recip (a + 3) (pos_a3 a) else Frac.zero)
                    (if b4 then Frac.recip (a + 4) (pos_a4 a) else Frac.zero))))
      ⟨(if b1 then q1 a else 0)
          + ((if b2 then q2 a else 0) + ((if b3 then q3 a else 0) + (if b4 then q4 a else 0))),
        D5 a, D5pos a ha⟩ :=
    Frac.add_common (D5pos a ha) (t1_eqv a ha b1) h234
  exact Frac.add_common (D5pos a ha) (t0_eqv a ha b0) h1234

/-- **The bridge.**  The reciprocals of the selected denominators sum to one
*iff* the cleared natural-number equation `cleared a b = D5 a` holds. -/
theorem sums_to_one_iff (a : Nat) (ha : 2 ≤ a) (b0 b1 b2 b3 b4 : Bool) :
    Frac.eqv (selSum a ha b0 b1 b2 b3 b4) Frac.one
      ↔ cleared a b0 b1 b2 b3 b4 = D5 a := by
  have key : Frac.eqv (selSum a ha b0 b1 b2 b3 b4) Frac.one ↔
      Frac.eqv ⟨cleared a b0 b1 b2 b3 b4, D5 a, D5pos a ha⟩ Frac.one := by
    constructor
    · intro h
      exact Frac.eqv_trans (Frac.eqv_symm (selSum_eqv_cleared a ha b0 b1 b2 b3 b4)) h
    · intro h
      exact Frac.eqv_trans (selSum_eqv_cleared a ha b0 b1 b2 b3 b4) h
  rw [key, Frac.eq_one_iff (D5pos a ha)]

/-! ## 4. The estimate for large `a` -/

private theorem mul_mono {a b c d : Nat} (h1 : a ≤ b) (h2 : c ≤ d) : a * c ≤ b * d :=
  Nat.le_trans (Nat.mul_le_mul_right c h1) (Nat.mul_le_mul_left b h2)

theorem q0_pos (a : Nat) : 0 < q0 a := by
  show 0 < ((a + 1) * (a + 2)) * (a + 3) * (a + 4)
  exact Nat.mul_pos
    (Nat.mul_pos (Nat.mul_pos (pos_a1 a) (pos_a2 a)) (pos_a3 a))
    (pos_a4 a)

theorem q1_le_q0 (a : Nat) : q1 a ≤ q0 a :=
  Nat.mul_le_mul_right (a + 4)
    (Nat.mul_le_mul_right (a + 3) (mul_mono (Nat.le_add_right a 1) (Nat.le_refl (a + 2))))

theorem q2_le_q0 (a : Nat) : q2 a ≤ q0 a :=
  Nat.mul_le_mul_right (a + 4)
    (Nat.mul_le_mul_right (a + 3) (mul_mono (Nat.le_add_right a 1) (Nat.le_add_right (a + 1) 1)))

theorem q3_le_q0 (a : Nat) : q3 a ≤ q0 a :=
  Nat.mul_le_mul_right (a + 4)
    (mul_mono (mul_mono (Nat.le_add_right a 1) (Nat.le_add_right (a + 1) 1))
      (Nat.le_add_right (a + 2) 1))

theorem q4_le_q0 (a : Nat) : q4 a ≤ q0 a :=
  mul_mono
    (mul_mono (mul_mono (Nat.le_add_right a 1) (Nat.le_add_right (a + 1) 1))
      (Nat.le_add_right (a + 2) 1))
    (Nat.le_add_right (a + 3) 1)

theorem cleared_le (a : Nat) (b0 b1 b2 b3 b4 : Bool) :
    cleared a b0 b1 b2 b3 b4 ≤ q0 a + (q0 a + (q0 a + (q0 a + q0 a))) := by
  have g0 : (if b0 then q0 a else 0) ≤ q0 a := by
    cases b0 <;> first | exact Nat.zero_le _ | exact Nat.le_refl _
  have g1 : (if b1 then q1 a else 0) ≤ q0 a := by
    cases b1 <;> first | exact Nat.zero_le _ | exact q1_le_q0 a
  have g2 : (if b2 then q2 a else 0) ≤ q0 a := by
    cases b2 <;> first | exact Nat.zero_le _ | exact q2_le_q0 a
  have g3 : (if b3 then q3 a else 0) ≤ q0 a := by
    cases b3 <;> first | exact Nat.zero_le _ | exact q3_le_q0 a
  have g4 : (if b4 then q4 a else 0) ≤ q0 a := by
    cases b4 <;> first | exact Nat.zero_le _ | exact q4_le_q0 a
  exact Nat.add_le_add g0 (Nat.add_le_add g1 (Nat.add_le_add g2 (Nat.add_le_add g3 g4)))

/-- For `a ≥ 6` even the sum of **all five** reciprocals is `< 1`. -/
theorem cleared_lt (a : Nat) (h6 : 6 ≤ a) (b0 b1 b2 b3 b4 : Bool) :
    cleared a b0 b1 b2 b3 b4 < D5 a := by
  have h5 : 5 < a := by omega
  have hsum : q0 a + (q0 a + (q0 a + (q0 a + q0 a))) = 5 * q0 a := by omega
  have hlt : 5 * q0 a < a * q0 a := Nat.mul_lt_mul_of_pos_right h5 (q0_pos a)
  have key : cleared a b0 b1 b2 b3 b4 < a * q0 a := by
    have s : cleared a b0 b1 b2 b3 b4 ≤ 5 * q0 a := by
      rw [← hsum]
      exact cleared_le a b0 b1 b2 b3 b4
    exact Nat.lt_of_le_of_lt s hlt
  rw [mul_q0] at key
  exact key

/-- A fixed proof of `2 ≤ 2`, used so that every statement about the window
`{2, …, 6}` mentions the *same* proof term. -/
theorem two_le_two : 2 ≤ (2 : Nat) := Nat.le_refl 2

/-! ## 5. The three main theorems -/

/-- **No interval of diameter `4` starting at `a ≥ 3` works.**
Since every interval of diameter `≤ 3` starting at `a ≥ 3` is contained in
`{a, …, a+4}`, this also rules out all shorter intervals with `a ≥ 3`. -/
theorem no_diameter_four_ge_three (a : Nat) (ha : 2 ≤ a) (h3 : 3 ≤ a)
    (b0 b1 b2 b3 b4 : Bool) :
    ¬ Frac.eqv (selSum a ha b0 b1 b2 b3 b4) Frac.one := by
  rw [sums_to_one_iff a ha b0 b1 b2 b3 b4]
  by_cases h : a ≤ 5
  · have : a = 3 ∨ a = 4 ∨ a = 5 := by omega
    rcases this with rfl | rfl | rfl
    all_goals
      cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide
  · exact Nat.ne_of_lt (cleared_lt a (by omega) b0 b1 b2 b3 b4)

/-- **No interval of diameter `≤ 3` works, for any starting point `a ≥ 2`.**
A subset of `[a, a+d]` with `d ≤ 3` is a subset of `{a, a+1, a+2, a+3}`, i.e.
it is `selSum a ha b0 b1 b2 b3 false` for the corresponding membership flags. -/
theorem no_diameter_three (a : Nat) (ha : 2 ≤ a) (b0 b1 b2 b3 : Bool) :
    ¬ Frac.eqv (selSum a ha b0 b1 b2 b3 false) Frac.one := by
  by_cases h : 3 ≤ a
  · exact no_diameter_four_ge_three a ha h b0 b1 b2 b3 false
  · have h2 : a = 2 := by omega
    subst h2
    rw [sums_to_one_iff 2 ha b0 b1 b2 b3 false]
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

/-- **`[2, 6]` works.**  `1/2 + 1/3 + 1/6 = 1`; the selected denominators are
`2, 3, 6`, i.e. flags `true, true, false, false, true` on the window
`{2, 3, 4, 5, 6}`. -/
theorem two_six_works :
    Frac.eqv (selSum 2 two_le_two true true false false true) Frac.one := by
  rw [sums_to_one_iff 2 two_le_two true true false false true]
  decide

/-- **Uniqueness inside `[2, 6]`.**  Among all 32 subsets of `{2,3,4,5,6}`,
`{2, 3, 6}` is the only one whose reciprocals sum to one. -/
theorem unique_subset_of_two_six (b0 b1 b2 b3 b4 : Bool) :
    Frac.eqv (selSum 2 two_le_two b0 b1 b2 b3 b4) Frac.one
      ↔ b0 = true ∧ b1 = true ∧ b2 = false ∧ b3 = false ∧ b4 = true := by
  rw [sums_to_one_iff 2 two_le_two b0 b1 b2 b3 b4]
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

/-! ## 6. The answer, stated once -/

/-- **Answer to JSP-000243.**

An *interval of denominators* here means a set `S` of distinct integers, all
lying in `[a, a + d]` for some `a ≥ 2`, whose reciprocals sum to `1`; `d` is the
diameter (length) of the interval.  Such sets are exactly the values of
`selSum a ha b₀ b₁ b₂ b₃ b₄` (the five Booleans range over all subsets of the
window `{a, …, a+4}`, and `b₄ = false` restricts to windows of diameter `≤ 3`).

Then:

* diameter `≤ 3` is impossible, whatever the starting point (`no_diameter_three`);
* diameter `4` is impossible unless the interval starts at `a = 2`
  (`no_diameter_four_ge_three`);
* `[2, 6]` does work (`two_six_works`), and inside it `{2, 3, 6}` is the unique
  choice (`unique_subset_of_two_six`).

Hence the shortest integer interval containing distinct denominators whose
reciprocals sum to one is **`[2, 6]`** — diameter `4`, five integers — realised
uniquely by **`1/2 + 1/3 + 1/6 = 1`**. -/
theorem shortest_interval_is_two_six :
    -- (i) an interval of diameter 4 exists that works, namely [2, 6]
    Frac.eqv (selSum 2 two_le_two true true false false true) Frac.one
    -- (ii) no interval of diameter ≤ 3 works, for any start a ≥ 2
    ∧ (∀ (a : Nat) (ha : 2 ≤ a) (b0 b1 b2 b3 : Bool),
        ¬ Frac.eqv (selSum a ha b0 b1 b2 b3 false) Frac.one)
    -- (iii) no interval of diameter 4 works unless it starts at 2
    ∧ (∀ (a : Nat) (ha : 2 ≤ a) (h3 : 3 ≤ a) (b0 b1 b2 b3 b4 : Bool),
        ¬ Frac.eqv (selSum a ha b0 b1 b2 b3 b4) Frac.one)
    -- (iv) inside [2, 6] the witness {2, 3, 6} is unique
    ∧ (∀ b0 b1 b2 b3 b4 : Bool,
        Frac.eqv (selSum 2 two_le_two b0 b1 b2 b3 b4) Frac.one
          ↔ b0 = true ∧ b1 = true ∧ b2 = false ∧ b3 = false ∧ b4 = true) :=
  ⟨two_six_works,
   fun a ha => no_diameter_three a ha,
   fun a ha h3 => no_diameter_four_ge_three a ha h3,
   unique_subset_of_two_six⟩

end Jsp000243
