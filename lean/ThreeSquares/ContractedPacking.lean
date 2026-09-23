import ThreeSquares.CenterBounds
import ThreeSquares.ContractedSyntax
import ThreeSquares.PackingCertificate

/-! Every smaller FC packing lies in the contracted domain and satisfies
additional radial and distance constraints. No global lower bound is assumed. -/

open scoped NNReal
open SquarePacking

namespace ThreeSquares.PackingFormula

private theorem eval_centers_contracted {r : ℝ≥0} (P : EdgeConstraintPacking 3 r) (i : Fin 3) :
    (centerX i).eval (assignment P) = P.centers i 0 ∧
    (centerY i).eval (assignment P) = P.centers i 1 := by
  fin_cases i <;> simp [centerX, centerY, IntervalExpr.eval, assignment]

private theorem eval_frame_contracted {r : ℝ≥0} (P : EdgeConstraintPacking 3 r)
    (hP : P.coefficients 0 = identityCoefficients) (i : Fin 3) :
    (frame i).a.eval (assignment P) = (P.coefficients i).a ∧
    (frame i).b.eval (assignment P) = (P.coefficients i).b ∧
    (frame i).c.eval (assignment P) = (P.coefficients i).c ∧
    (frame i).d.eval (assignment P) = (P.coefficients i).d := by
  fin_cases i <;> simp [frame, IntervalExpr.eval, assignment, hP, identityCoefficients]

theorem centerSquared_eval {r : ℝ≥0} (P : EdgeConstraintPacking 3 r) (i : Fin 3) :
    (centerSquared i).eval (assignment P) = (P.centers i 0) ^ 2 + (P.centers i 1) ^ 2 := by
  have hc := eval_centers_contracted P i
  simp only [centerSquared, IntervalExpr.eval, hc.1, hc.2]

theorem centerDisk_holds {r : ℝ≥0} (P : EdgeConstraintPacking 3 r) (hr : r < radius)
    (i : Fin 3) : (centerDisk i).Holds (assignment P) := by
  have hn := center_norm_lt_eleven_sixteenths (P.vertices i) hr
  have hs := pow_le_pow_left₀ (norm_nonneg (P.centers i)) (le_of_lt hn) 2
  rw [plane_norm_sq] at hs
  simp only [centerDisk, le, sub, IntervalFormula.Holds, IntervalExpr.eval, centerSquared_eval]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  nlinarith only [hs]

theorem centerDistance_holds {r : ℝ≥0} (P : EdgeConstraintPacking 3 r)
    (i j : Fin 3) (hij : i < j) : (centerDistance i j).Holds (assignment P) := by
  have hi := eval_centers_contracted P i
  have hj := eval_centers_contracted P j
  have hs := separated_centers_distance_sq (P.separations i j hij)
  simp only [centerDistance, le, sub, IntervalFormula.Holds, IntervalExpr.eval,
    hi.1, hi.2, hj.1, hj.2, Rat.cast_one]
  nlinarith only [hs]

theorem radialMax_holds {r : ℝ≥0} (P : EdgeConstraintPacking 3 r)
    (hP : P.coefficients 0 = identityCoefficients) (i : Fin 3) :
    (radialMax i).Holds (assignment P) := by
  have hc := eval_centers_contracted P i
  have hf := eval_frame_contracted P hP i
  have hv := vertex_bound_max ((inside_iff_four_vertex_bounds r _ _).mp
    (P.toCoefficients.inside i))
  dsimp only [EdgeConstraintPacking.toCoefficients] at hv
  have hs : assignment P 14 = (r : ℝ) ^ 2 := rfl
  simp only [radialMax, le, sub, IntervalFormula.Holds, IntervalExpr.eval,
    centerSquared_eval, hc.1, hc.2, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2, hs]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  linarith only [hv]

theorem contractedFormula_holds {r : ℝ≥0} (P : EdgeConstraintPacking 3 r)
    (hP : P.coefficients 0 = identityCoefficients) (hr : r < radius) :
    contractedFormula.Holds (assignment P) := by
  exact ⟨centerDistance_holds P 0 1 (by decide), centerDistance_holds P 0 2 (by decide),
    centerDistance_holds P 1 2 (by decide), centerDisk_holds P hr 0,
    centerDisk_holds P hr 1, centerDisk_holds P hr 2, radialMax_holds P hP 0,
    radialMax_holds P hP 1, radialMax_holds P hP 2, smaller_formula_holds P hP hr⟩

theorem assignment_in_contractedBox {r : ℝ≥0} (P : EdgeConstraintPacking 3 r)
    (hr : r < radius) : contractedBox.Contains (assignment P) := by
  have hc (i : Fin 3) (k : Fin 2) : -(11 / 16) ≤ P.centers i k ∧ P.centers i k ≤ 11 / 16 :=
    abs_le.mp (le_of_lt (center_coordinate_lt_eleven_sixteenths (P.vertices i) hr k))
  have hf (i : Fin 3) := (P.coefficients i).entries_bounded
  have hslo := radius_sq_ge_half (P.vertices 0)
  have hr' : (r : ℝ) < (radius : ℝ) := by exact_mod_cast hr
  have hshi : (r : ℝ) ^ 2 ≤ 425 / 256 := by
    nlinarith [radius_sq_real, r.coe_nonneg, radius.coe_nonneg]
  intro i
  fin_cases i <;> norm_num [contractedBox, RationalInterval.Contains, assignment]
  · exact hc 0 0
  · exact hc 0 1
  · exact hc 1 0
  · exact hc 1 1
  · exact hc 2 0
  · exact hc 2 1
  · exact abs_le.mp (hf 1).1
  · exact abs_le.mp (hf 1).2.1
  · exact abs_le.mp (hf 1).2.2.1
  · exact abs_le.mp (hf 1).2.2.2
  · exact abs_le.mp (hf 2).1
  · exact abs_le.mp (hf 2).2.1
  · exact abs_le.mp (hf 2).2.2.1
  · exact abs_le.mp (hf 2).2.2.2
  · exact ⟨hslo, hshi⟩

theorem contractedBox_subset_initialBox {x : Fin 15 → ℝ}
    (h : contractedBox.Contains x) : initialBox.Contains x := by
  intro i
  have hi := h i
  fin_cases i <;> norm_num [contractedBox, initialBox, RationalInterval.Contains] at hi ⊢ <;>
    constructor <;> linarith

theorem smaller_fc_packing_has_contracted_assignment {r : ℝ≥0} (hr : r < radius)
    (h : Nonempty (Packing 3 UnitSquare (Circle r))) :
    ∃ x : Fin 15 → ℝ, contractedBox.Contains x ∧ contractedFormula.Holds x := by
  obtain ⟨P, hP⟩ := (normalized_edge_constraints_packing_iff 3 r 0).mpr h
  exact ⟨assignment P, assignment_in_contractedBox P hr, contractedFormula_holds P hP hr⟩

theorem contracted_certificate_localizes_smaller_fc_packing (t : IntervalCertificate 15)
    (hcheck : t.check contractedFormula contractedBox = true) {r : ℝ≥0} (hr : r < radius)
    (h : Nonempty (Packing 3 UnitSquare (Circle r))) :
    ∃ x : Fin 15 → ℝ, ∃ C ∈ t.residuals contractedBox,
      C.Contains x ∧ contractedFormula.Holds x := by
  obtain ⟨x, hx, hp⟩ := smaller_fc_packing_has_contracted_assignment hr h
  obtain ⟨C, hC, hCx⟩ := t.check_sound contractedFormula hcheck hx hp
  exact ⟨x, C, hC, hCx, hp⟩

theorem global_lower_bound_of_empty_contracted_certificate (t : IntervalCertificate 15)
    (hcheck : t.check contractedFormula contractedBox = true)
    (hempty : t.residuals contractedBox = []) : GlobalLowerBound := by
  intro r hr
  by_contra hn
  exact t.exclude_sound contractedFormula hcheck hempty
    (smaller_fc_packing_has_contracted_assignment (lt_of_not_ge hn) hr)

end ThreeSquares.PackingFormula
