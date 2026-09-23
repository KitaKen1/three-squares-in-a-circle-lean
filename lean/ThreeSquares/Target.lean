import ThreeSquares.UpperBound
import ThreeSquares.FiniteParameters
import ThreeSquares.FiniteConstraints
import ThreeSquares.EdgeConstraints

/-! # The FC target and finite-model equivalences

This module defines the exact FC feasible-radius set and proves equivalences
between its `IsLeast` statement and several normalized finite models. The
conditional assembly lemma is retained as a useful bridge; the unconditional
global lower bound and final FC theorem are proved by the checked representative
trees in `ThreeSquares.RepTrees`.
-/

open scoped NNReal
open SquarePacking

namespace ThreeSquares

def feasibleRadii : Set ℝ≥0 := {r | Nonempty (Packing 3 UnitSquare (Circle r))}

def GlobalLowerBound : Prop := ∀ r ∈ feasibleRadii, radius ≤ r

/-- The same obligation in finite coordinates with the first frame fixed. -/
def NormalizedLowerBound : Prop := ∀ (r : ℝ≥0) (P : CoefficientPacking 3 r),
  P.coefficients 0 = identityCoefficients → radius ≤ r

theorem global_lower_bound_iff_normalized : GlobalLowerBound ↔ NormalizedLowerBound := by
  constructor
  · intro h r P _
    exact h r ⟨P.toFramed.toPacking⟩
  · intro h r hr
    obtain ⟨P, hP⟩ := (normalized_coefficient_packing_iff 3 r 0).mpr hr
    exact h r P hP

theorem global_lower_bound_iff_no_smaller_normalized :
    GlobalLowerBound ↔ ¬ ∃ r : ℝ≥0, r < radius ∧
      ∃ P : CoefficientPacking 3 r, P.coefficients 0 = identityCoefficients := by
  rw [global_lower_bound_iff_normalized]
  constructor
  · rintro h ⟨r, hr, P, hP⟩
    exact (not_lt_of_ge (h r P hP)) hr
  · intro h r P hP
    by_contra hn
    exact h ⟨r, lt_of_not_ge hn, P, hP⟩

theorem radius_feasible : radius ∈ feasibleRadii := ⟨canonicalPacking⟩

theorem global_lower_bound_iff_no_smaller_finite_constraints :
    GlobalLowerBound ↔ ¬ ∃ r : ℝ≥0, r < radius ∧
      ∃ P : FiniteConstraintPacking 3 r, P.coefficients 0 = identityCoefficients := by
  constructor
  · rintro h ⟨r, hr, P, _⟩
    exact (not_lt_of_ge (h r ⟨P.toCoefficients.toFramed.toPacking⟩)) hr
  · intro h r hr
    by_contra hn
    obtain ⟨P, hP⟩ := (normalized_finite_constraints_packing_iff 3 r 0).mpr hr
    exact h ⟨r, lt_of_not_ge hn, P, hP⟩

theorem least_radius_iff_global_lower_bound :
    IsLeast feasibleRadii radius ↔ GlobalLowerBound := by
  constructor
  · intro h r hr
    exact h.2 hr
  · intro h
    exact ⟨radius_feasible, fun r hr => h r hr⟩

/-- The unrestricted lower bound is exactly the absence of a smaller-radius
solution of the finite model with four edge axes and no separator variables. -/
theorem global_lower_bound_iff_no_smaller_edge_constraints :
    GlobalLowerBound ↔ ¬ ∃ r : ℝ≥0, r < radius ∧
      ∃ P : EdgeConstraintPacking 3 r, P.coefficients 0 = identityCoefficients := by
  constructor
  · rintro h ⟨r, hr, P, _⟩
    exact (not_lt_of_ge (h r ⟨P.toCoefficients.toFramed.toPacking⟩)) hr
  · intro h r hr
    by_contra hn
    obtain ⟨P, hP⟩ := (normalized_edge_constraints_packing_iff 3 r 0).mpr hr
    exact h ⟨r, lt_of_not_ge hn, P, hP⟩

/-- A conditional assembly theorem. `hlower` remains the research obligation. -/
theorem least_three_square_packing_in_circle_of_lower_bound
    (hlower : GlobalLowerBound) :
    IsLeast {r : ℝ≥0 | Nonempty (Packing 3 UnitSquare (Circle r))}
      ((5 * NNReal.sqrt 17) / 16) :=
  least_radius_iff_global_lower_bound.mpr hlower

end ThreeSquares
