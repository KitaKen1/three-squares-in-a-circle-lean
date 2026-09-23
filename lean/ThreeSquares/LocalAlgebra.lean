import ThreeSquares.AxisAligned

/-! # The finite algebraic part of the reported local rigidity argument

The inequalities are explicit hypotheses, not axioms. This file proves their
algebraic consequences. `ThreeSquares.LocalGeometry` derives them from actual
square constraints in a normalized matrix-entry neighborhood.
-/

noncomputable section

namespace ThreeSquares

/-- Seven necessary inequalities as stated in the round 55 interval report. -/
structure LocalConstraints (E x₁ y₁ x₂ y₂ x₃ y₃ α β : ℝ) : Prop where
  disk₁ : -2 * x₁ - 13 / 8 * y₁ - 3 / 16 * α ≤ E
  disk₂ : 2 * x₂ - 13 / 8 * y₂ + 3 / 16 * β ≤ E
  disk₃plus : x₃ + 19 / 8 * y₃ ≤ E
  disk₃minus : -x₃ + 19 / 8 * y₃ ≤ E
  separation₁₂ : |β - α| / 2 - E ≤ x₂ - x₁
  separation₁₃ : max α 0 / 2 - E ≤ y₃ - y₁
  separation₂₃ : max (-β) 0 / 2 - E ≤ y₃ - y₂

theorem angle_abs_identity (α β : ℝ) :
    |α| + |β| = 2 * (max α 0 + max (-β) 0) + (β - α) := by
  rcases le_total 0 α with ha | ha <;> rcases le_total 0 β with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb, max_eq_left ha,
      max_eq_right (neg_nonpos.mpr hb)]
    ring
  · rw [abs_of_nonneg ha, abs_of_nonpos hb, max_eq_left ha,
      max_eq_left (neg_nonneg.mpr hb)]
    ring
  · rw [abs_of_nonpos ha, abs_of_nonneg hb, max_eq_right ha,
      max_eq_right (neg_nonpos.mpr hb)]
    ring
  · rw [abs_of_nonpos ha, abs_of_nonpos hb, max_eq_right ha,
      max_eq_left (neg_nonneg.mpr hb)]
    ring

/-- The seven inequalities themselves force a nonnegative common error budget. -/
theorem local_error_nonneg {E x₁ y₁ x₂ y₂ x₃ y₃ α β : ℝ}
    (h : LocalConstraints E x₁ y₁ x₂ y₂ x₃ y₃ α β) : 0 ≤ E := by
  rcases h with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  have hA₀ : 0 ≤ max α 0 := le_max_right _ _
  have hB₀ : 0 ≤ max (-β) 0 := le_max_right _ _
  have hd₂ : -(β - α) ≤ |β - α| := neg_le_abs _
  have hd₀ : 0 ≤ |β - α| := abs_nonneg _
  linarith

theorem local_coordinate_bounds {E x₁ y₁ x₂ y₂ x₃ y₃ α β : ℝ}
    (hE : 0 ≤ E) (h : LocalConstraints E x₁ y₁ x₂ y₂ x₃ y₃ α β) :
    |x₁| ≤ 26 * E ∧ |y₁| ≤ 26 * E ∧ |x₂| ≤ 26 * E ∧ |y₂| ≤ 26 * E ∧
    |x₃| ≤ 26 * E ∧ |y₃| ≤ 26 * E ∧ |α| ≤ 26 * E ∧ |β| ≤ 26 * E := by
  rcases h with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  have hA₀ : 0 ≤ max α 0 := le_max_right _ _
  have hB₀ : 0 ≤ max (-β) 0 := le_max_right _ _
  have hαmax : α ≤ max α 0 := le_max_left _ _
  have hβmax : -β ≤ max (-β) 0 := le_max_left _ _
  have hd₁ : β - α ≤ |β - α| := le_abs_self _
  have hd₂ : -(β - α) ≤ |β - α| := neg_le_abs _
  have hd₀ : 0 ≤ |β - α| := abs_nonneg _
  have hcombined : |β - α| + 3 / 16 * (β - α) +
      13 / 16 * (max α 0 + max (-β) 0) ≤ 21 / 2 * E := by
    linarith
  have hbudget : |β - α| + max α 0 + max (-β) 0 ≤ 13 * E := by
    linarith
  have hid := angle_abs_identity α β
  have hα₀ := abs_nonneg α
  have hβ₀ := abs_nonneg β
  have hαbound : |α| ≤ 26 * E := by linarith
  have hβbound : |β| ≤ 26 * E := by linarith
  have hαlow := (abs_le.mp hαbound).1
  have hαhigh := (abs_le.mp hαbound).2
  have hβlow := (abs_le.mp hβbound).1
  have hβhigh := (abs_le.mp hβbound).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hαbound, hβbound⟩ <;>
    apply abs_le.mpr <;> constructor <;> linarith

/-- A sharper common constant for the same seven inequalities.  The proof is
still purely linear; no geometric hypothesis is hidden here. -/
theorem local_coordinate_bounds_eleven {E x₁ y₁ x₂ y₂ x₃ y₃ α β : ℝ}
    (hE : 0 ≤ E) (h : LocalConstraints E x₁ y₁ x₂ y₂ x₃ y₃ α β) :
    |x₁| ≤ 11 * E ∧ |y₁| ≤ 11 * E ∧ |x₂| ≤ 11 * E ∧ |y₂| ≤ 11 * E ∧
    |x₃| ≤ 11 * E ∧ |y₃| ≤ 11 * E ∧ |α| ≤ 11 * E ∧ |β| ≤ 11 * E := by
  rcases h with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  have hd₁ := le_abs_self (β - α)
  have hd₂ := neg_le_abs (β - α)
  have hα₁ := le_max_left α 0
  have hα₂ := le_max_right α 0
  have hβ₁ := le_max_left (-β) 0
  have hβ₂ := le_max_right (-β) 0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply abs_le.mpr <;> constructor <;> linarith

def perturbation (x₁ y₁ x₂ y₂ x₃ y₃ α β : ℝ) : ℝ :=
  max |x₁| (max |y₁| (max |x₂| (max |y₂| (max |x₃| (max |y₃| (max |α| |β|))))))

theorem perturbation_nonneg (x₁ y₁ x₂ y₂ x₃ y₃ α β : ℝ) :
    0 ≤ perturbation x₁ y₁ x₂ y₂ x₃ y₃ α β :=
  (abs_nonneg x₁).trans (le_max_left _ _)

theorem local_perturbation_bound {E x₁ y₁ x₂ y₂ x₃ y₃ α β : ℝ}
    (hE : 0 ≤ E) (h : LocalConstraints E x₁ y₁ x₂ y₂ x₃ y₃ α β) :
    perturbation x₁ y₁ x₂ y₂ x₃ y₃ α β ≤ 26 * E := by
  simpa only [perturbation, max_le_iff] using local_coordinate_bounds hE h

theorem local_perturbation_bound_eleven {E x₁ y₁ x₂ y₂ x₃ y₃ α β : ℝ}
    (hE : 0 ≤ E) (h : LocalConstraints E x₁ y₁ x₂ y₂ x₃ y₃ α β) :
    perturbation x₁ y₁ x₂ y₂ x₃ y₃ α β ≤ 11 * E := by
  simpa only [perturbation, max_le_iff] using local_coordinate_bounds_eleven hE h

/-- The contraction inequality has no positive solution in the stated neighborhood. -/
theorem small_quadratic_forces_zero {ε : ℝ} (h₀ : 0 ≤ ε)
    (hsmall : ε ≤ 1 / 1000) (h : ε ≤ 260 * ε ^ 2) : ε = 0 := by
  have hprod : ε * (1 / 1000 - ε) ≥ 0 := mul_nonneg h₀ (sub_nonneg.mpr hsmall)
  nlinarith

/-- The algebraic local rigidity conclusion, conditional on the seven geometric inequalities. -/
theorem local_algebra_rigidity {x₁ y₁ x₂ y₂ x₃ y₃ α β : ℝ}
    (hsmall : perturbation x₁ y₁ x₂ y₂ x₃ y₃ α β ≤ 1 / 1000)
    (h : LocalConstraints (10 * perturbation x₁ y₁ x₂ y₂ x₃ y₃ α β ^ 2)
      x₁ y₁ x₂ y₂ x₃ y₃ α β) :
    x₁ = 0 ∧ y₁ = 0 ∧ x₂ = 0 ∧ y₂ = 0 ∧ x₃ = 0 ∧ y₃ = 0 ∧ α = 0 ∧ β = 0 := by
  have hE : 0 ≤ 10 * perturbation x₁ y₁ x₂ y₂ x₃ y₃ α β ^ 2 := by positivity
  have hp := local_perturbation_bound hE h
  have hz : perturbation x₁ y₁ x₂ y₂ x₃ y₃ α β = 0 :=
    small_quadratic_forces_zero (perturbation_nonneg ..) hsmall (by nlinarith [hp])
  have hb := local_coordinate_bounds hE h
  rw [hz] at hb
  norm_num only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, abs_nonpos_iff] at hb
  exact hb

/-- The improved linear estimate closes the larger dyadic neighborhood needed
by the matrix-entry formulation of local geometry. -/
theorem local_algebra_rigidity_four {x₁ y₁ x₂ y₂ x₃ y₃ α β : ℝ}
    (hsmall : perturbation x₁ y₁ x₂ y₂ x₃ y₃ α β ≤ 1 / 64)
    (h : LocalConstraints (4 * perturbation x₁ y₁ x₂ y₂ x₃ y₃ α β ^ 2)
      x₁ y₁ x₂ y₂ x₃ y₃ α β) :
    x₁ = 0 ∧ y₁ = 0 ∧ x₂ = 0 ∧ y₂ = 0 ∧ x₃ = 0 ∧ y₃ = 0 ∧ α = 0 ∧ β = 0 := by
  have hE : 0 ≤ 4 * perturbation x₁ y₁ x₂ y₂ x₃ y₃ α β ^ 2 := by positivity
  have hp := local_perturbation_bound_eleven hE h
  have h₀ := perturbation_nonneg x₁ y₁ x₂ y₂ x₃ y₃ α β
  have hm := mul_nonneg h₀ (sub_nonneg.mpr hsmall)
  have hz : perturbation x₁ y₁ x₂ y₂ x₃ y₃ α β = 0 := by nlinarith
  have hb := local_coordinate_bounds_eleven hE h
  rw [hz] at hb
  norm_num only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, abs_nonpos_iff] at hb
  exact hb

/-- Quantitative stability for the same explicit algebraic constraints.
The hypotheses must still be derived from geometry before using this for packings. -/
theorem local_algebra_stability {δ x₁ y₁ x₂ y₂ x₃ y₃ α β : ℝ}
    (hsmall : perturbation x₁ y₁ x₂ y₂ x₃ y₃ α β ≤ 1 / 1000)
    (h : LocalConstraints (10 * perturbation x₁ y₁ x₂ y₂ x₃ y₃ α β ^ 2 + δ)
      x₁ y₁ x₂ y₂ x₃ y₃ α β) :
    37 / 1300 * perturbation x₁ y₁ x₂ y₂ x₃ y₃ α β ≤ δ := by
  have hp := local_perturbation_bound (local_error_nonneg h) h
  have h₀ := perturbation_nonneg x₁ y₁ x₂ y₂ x₃ y₃ α β
  have hm := mul_nonneg h₀ (sub_nonneg.mpr hsmall)
  nlinarith

end ThreeSquares
