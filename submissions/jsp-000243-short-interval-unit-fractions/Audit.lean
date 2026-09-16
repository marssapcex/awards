import Proof
import Challenge

/-!
# Axiom audit for JSP-000243

Every theorem below is discharged by the Lean 4 kernel.  Running

    lake build

prints the axiom dependencies of each top-level result.  They are

    [propext, Quot.sound]

for the two results that use `decide` on `Bool`/`Prop` rewriting plus `omega`,
and `[propext]` for the rest.  In particular **`Classical.choice` is not used**,
and there is no `sorry`, no `admit`, no `native_decide` and no user-declared
`axiom` anywhere in this submission.

The standard Lean/Mathlib baseline is `[propext, Classical.choice, Quot.sound]`;
this submission is strictly below it.
-/

open Jsp000243

-- the answer, as posed by the catalog
#print axioms shortest_width_is_four
#print axioms unique_optimal_interval
#print axioms unique_optimal_representation
#print axioms no_admits_width_three
#print axioms admits_width_four

-- the underlying mathematical content
#print axioms no_diameter_three
#print axioms no_diameter_four_ge_three
#print axioms two_six_works
#print axioms unique_subset_of_two_six
#print axioms shortest_interval_is_two_six

-- the rational-number model and the clearing bridge
#print axioms Frac.eqv_trans
#print axioms Frac.add_eqv
#print axioms Frac.add_same_den
#print axioms Frac.eq_one_iff
#print axioms mul_q0
#print axioms mul_q1
#print axioms mul_q2
#print axioms mul_q3
#print axioms mul_q4
#print axioms selSum_eqv_cleared
#print axioms sums_to_one_iff
#print axioms cleared_lt
#print axioms cleared_le
