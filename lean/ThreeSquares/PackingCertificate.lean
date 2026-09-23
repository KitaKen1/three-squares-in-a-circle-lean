import ThreeSquares.PackingFormula
import ThreeSquares.Target

/-! # Initial coverage and the remaining certificate obligation

Every FC packing below the candidate radius produces a solution of the
checker formula in the explicit rational box [-2,2]^15. An accepted tree
localizes every such solution into its retained leaves. An accepted tree
with no retained leaves would prove the global lower bound; this file does
not supply such a tree.
-/

open scoped NNReal
open SquarePacking

namespace ThreeSquares
namespace PackingFormula

theorem assignment_in_initialBox {r : ℝ≥0} (P : EdgeConstraintPacking 3 r)
    (hr : r < radius) : initialBox.Contains (assignment P) := by
  have hr' : (r : ℝ) < (radius : ℝ) := by exact_mod_cast hr
  have hr2 : (r : ℝ) ^ 2 < 425 / 256 := by
    nlinarith [radius_sq_real, r.coe_nonneg, radius.coe_nonneg]
  have hc (i : Fin 3) : (-2 ≤ P.centers i 0 ∧ P.centers i 0 ≤ 2) ∧
      (-2 ≤ P.centers i 1 ∧ P.centers i 1 ≤ 2) := by
    have h := (mem_circle_iff_norm_sq _ _).mp (P.toCoefficients.toFramed.center_inside i)
    change ‖P.centers i‖ ^ 2 < (r : ℝ) ^ 2 at h
    rw [plane_norm_sq] at h
    constructor <;> constructor <;>
      nlinarith [sq_nonneg (P.centers i 0), sq_nonneg (P.centers i 1)]
  have hf (i : Fin 3) : (-2 ≤ (P.coefficients i).a ∧ (P.coefficients i).a ≤ 2) ∧
      (-2 ≤ (P.coefficients i).b ∧ (P.coefficients i).b ≤ 2) ∧
      (-2 ≤ (P.coefficients i).c ∧ (P.coefficients i).c ≤ 2) ∧
      (-2 ≤ (P.coefficients i).d ∧ (P.coefficients i).d ≤ 2) := by
    have h1 := (P.coefficients i).first_unit
    have h2 := (P.coefficients i).second_unit
    have ha := sq_nonneg (P.coefficients i).a
    have hb := sq_nonneg (P.coefficients i).b
    have hc := sq_nonneg (P.coefficients i).c
    have hd := sq_nonneg (P.coefficients i).d
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩,
      ⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
  have hs : -2 ≤ (r : ℝ) ^ 2 ∧ (r : ℝ) ^ 2 ≤ 2 :=
    ⟨by nlinarith [sq_nonneg (r : ℝ)], by linarith⟩
  intro i
  fin_cases i <;> norm_num only [initialBox, RationalInterval.Contains, assignment,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Rat.cast_neg, Rat.cast_ofNat]
  · exact (hc 0).1
  · exact (hc 0).2
  · exact (hc 1).1
  · exact (hc 1).2
  · exact (hc 2).1
  · exact (hc 2).2
  · exact (hf 1).1
  · exact (hf 1).2.1
  · exact (hf 1).2.2.1
  · exact (hf 1).2.2.2
  · exact (hf 2).1
  · exact (hf 2).2.1
  · exact (hf 2).2.2.1
  · exact (hf 2).2.2.2
  · exact hs

theorem smaller_formula_holds {r : ℝ≥0} (P : EdgeConstraintPacking 3 r)
    (hP : P.coefficients 0 = identityCoefficients) (hr : r < radius) :
    smallerFormula.Holds (assignment P) := by
  refine ⟨formula_holds P hP, ?_⟩
  have hr' : (r : ℝ) < (radius : ℝ) := by exact_mod_cast hr
  change (r : ℝ) ^ 2 + -((425 / 256 : ℚ) : ℝ) < 0
  norm_num
  nlinarith [radius_sq_real, r.coe_nonneg, radius.coe_nonneg]

theorem smaller_fc_packing_has_assignment {r : ℝ≥0} (hr : r < radius)
    (h : Nonempty (Packing 3 UnitSquare (Circle r))) :
    ∃ x : Fin 15 → ℝ, initialBox.Contains x ∧ smallerFormula.Holds x := by
  obtain ⟨P, hP⟩ := (normalized_edge_constraints_packing_iff 3 r 0).mpr h
  exact ⟨assignment P, assignment_in_initialBox P hr, smaller_formula_holds P hP hr⟩

theorem certificate_localizes_smaller_fc_packing (t : IntervalCertificate 15)
    (hcheck : t.check smallerFormula initialBox = true) {r : ℝ≥0} (hr : r < radius)
    (h : Nonempty (Packing 3 UnitSquare (Circle r))) :
    ∃ x : Fin 15 → ℝ, ∃ C ∈ t.residuals initialBox,
      C.Contains x ∧ smallerFormula.Holds x := by
  obtain ⟨x, hx, hp⟩ := smaller_fc_packing_has_assignment hr h
  obtain ⟨C, hC, hCx⟩ := t.check_sound smallerFormula hcheck hx hp
  exact ⟨x, C, hC, hCx, hp⟩

/-- Conditional assembly only: neither `hcheck` nor `hempty` is supplied for
the full initial domain. They must be proved for a concrete certificate. -/
theorem global_lower_bound_of_empty_certificate (t : IntervalCertificate 15)
    (hcheck : t.check smallerFormula initialBox = true) (hempty : t.residuals initialBox = []) :
    GlobalLowerBound := by
  intro r hr
  by_contra hn
  exact t.exclude_sound smallerFormula hcheck hempty
    (smaller_fc_packing_has_assignment (lt_of_not_ge hn) hr)

end PackingFormula
end ThreeSquares
