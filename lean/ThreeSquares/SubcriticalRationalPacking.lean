import ThreeSquares.RationalRotation
import ThreeSquares.Target

/-! # Eliminating the radius from a subcritical three-square packing

For excluding a packing below the candidate radius, the radius itself is not
needed: all twelve vertices must have squared norm strictly below `425 / 256`.
This module transfers every smaller FC packing to that exact eight-variable
model after normalizing the first square.
-/

open scoped NNReal
open SquarePacking

noncomputable section

namespace ThreeSquares

/-- The positive-determinant square frame represented by the rational
parameter `t`. -/
def rationalRotationCoefficients (t : ℝ) : OrthogonalCoefficients :=
  rotationCoefficients (rationalCos t) (rationalSin t) (rational_rotation_unit t)

/-- The four vertices lie strictly inside the circle at the candidate squared
radius. This condition has no radius variable. -/
def StrictCandidateVertexInequalities (c : Plane) (A : OrthogonalCoefficients) : Prop :=
  vertexSquared c A (-1 / 2) (-1 / 2) < 425 / 256 ∧
  vertexSquared c A (-1 / 2) (1 / 2) < 425 / 256 ∧
  vertexSquared c A (1 / 2) (-1 / 2) < 425 / 256 ∧
  vertexSquared c A (1 / 2) (1 / 2) < 425 / 256

theorem strict_candidate_vertex_bound_max {c : Plane} {A : OrthogonalCoefficients}
    (h : StrictCandidateVertexInequalities c A) :
    c 0 ^ 2 + c 1 ^ 2 + |c 0 * A.a + c 1 * A.c| +
      |c 0 * A.b + c 1 * A.d| + 1 / 2 < 425 / 256 := by
  obtain ⟨h₀₀, h₀₁, h₁₀, h₁₁⟩ := h
  rw [← norm_sq_eq_vertexSquared] at h₀₀ h₀₁ h₁₀ h₁₁
  rw [coefficient_norm_sq_expand] at h₀₀ h₀₁ h₁₀ h₁₁
  by_cases hx : 0 ≤ c 0 * A.a + c 1 * A.c <;>
    by_cases hy : 0 ≤ c 0 * A.b + c 1 * A.d
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]; nlinarith only [h₁₁]
  · rw [abs_of_nonneg hx, abs_of_neg (lt_of_not_ge hy)]; nlinarith only [h₁₀]
  · rw [abs_of_neg (lt_of_not_ge hx), abs_of_nonneg hy]; nlinarith only [h₀₁]
  · rw [abs_of_neg (lt_of_not_ge hx), abs_of_neg (lt_of_not_ge hy)]; nlinarith only [h₀₀]

theorem strict_candidate_center_radial_bound {c : Plane} {A : OrthogonalCoefficients}
    (h : StrictCandidateVertexInequalities c A) :
    ‖c‖ ^ 2 + ‖c‖ + 1 / 2 < 425 / 256 := by
  have hv := strict_candidate_vertex_bound_max h
  have hp := A.projection_l1_ge_norm c
  rw [← plane_norm_sq] at hv
  linarith only [hv, hp]

theorem strict_candidate_center_norm_lt {c : Plane} {A : OrthogonalCoefficients}
    (h : StrictCandidateVertexInequalities c A) : ‖c‖ < 11 / 16 := by
  have hb := strict_candidate_center_radial_bound h
  by_contra hn
  have hn' := le_of_not_gt hn
  nlinarith only [hb, hn', norm_nonneg c, sq_nonneg (‖c‖ - 11 / 16)]

theorem strict_candidate_center_coordinate_abs_lt {c : Plane}
    {A : OrthogonalCoefficients} (h : StrictCandidateVertexInequalities c A)
    (k : Fin 2) : |c k| < 11 / 16 :=
  (plane_coordinate_abs_le_norm c k).trans_lt (strict_candidate_center_norm_lt h)

/-- Radius-free necessary model for a packing strictly below the candidate
radius. For three normalized squares it has exactly eight configuration
variables: six center coordinates and two nonconstant rotation parameters. -/
structure SubcriticalRationalRotationPacking (n : ℕ) where
  centers : Fin n → Plane
  t : Fin n → ℝ
  t_nonneg : ∀ i, 0 ≤ t i
  t_le_one : ∀ i, t i ≤ 1
  vertices : ∀ i, StrictCandidateVertexInequalities
    (centers i) (rationalRotationCoefficients (t i))
  separations : ∀ i j, i < j → FourAxisSeparation
    (centers i) (centers j)
    (rationalRotationCoefficients (t i))
    (rationalRotationCoefficients (t j))

theorem squared_radius_lt_candidate {r : ℝ≥0} (hr : r < radius) :
    (r : ℝ) ^ 2 < 425 / 256 := by
  have hr' : (r : ℝ) < (radius : ℝ) := by exact_mod_cast hr
  nlinarith [radius_sq_real, r.coe_nonneg, radius.coe_nonneg]

/-- Forget the radius after strengthening each closed vertex inequality by
the strict gap between `r` and the candidate radius. -/
def RationalRotationPacking.toSubcritical {n : ℕ} {r : ℝ≥0}
    (P : RationalRotationPacking n r) (hr : r < radius) :
    SubcriticalRationalRotationPacking n where
  centers := P.centers
  t := P.t
  t_nonneg := P.t_nonneg
  t_le_one := P.t_le_one
  vertices i := by
    have h := P.vertices i
    have hr2 := squared_radius_lt_candidate hr
    change VertexInequalities r (P.centers i) (rationalRotationCoefficients (P.t i)) at h
    rcases h with ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨lt_of_le_of_lt h₁ hr2, lt_of_le_of_lt h₂ hr2,
      lt_of_le_of_lt h₃ hr2, lt_of_le_of_lt h₄ hr2⟩
  separations := P.separations

/-- Every FC packing below the candidate radius gives a normalized,
radius-free eight-variable model. -/
theorem normalized_subcritical_rational_model_of_packing {r : ℝ≥0}
    (hr : r < radius) (h : Nonempty (Packing 3 UnitSquare (Circle r))) :
    ∃ P : SubcriticalRationalRotationPacking 3, P.t 0 = 0 := by
  obtain ⟨P, hP⟩ := (normalized_rational_rotation_packing_iff 3 r 0).mpr h
  exact ⟨P.toSubcritical hr, hP⟩

/-- The complete radius-elimination implication used by a future global
certificate: a smaller FC packing would produce an eight-variable witness. -/
theorem smaller_fc_packing_has_eight_variable_witness :
    (∃ r : ℝ≥0, r < radius ∧ Nonempty (Packing 3 UnitSquare (Circle r))) →
      ∃ P : SubcriticalRationalRotationPacking 3, P.t 0 = 0 := by
  rintro ⟨r, hr, h⟩
  exact normalized_subcritical_rational_model_of_packing hr h

end ThreeSquares
