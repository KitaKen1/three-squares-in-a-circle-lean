import ThreeSquares.FiniteParameters
import ThreeSquares.RotatedVertices

/-! # Four closed vertex bounds characterize open-circle containment

For a nondegenerate unit square, strict interior containment follows even when
some vertices lie on the circle. The positive quadratic deficit in interior
coordinates provides the strict inequality.
-/

open scoped NNReal
open SquarePacking

noncomputable section

namespace ThreeSquares

theorem coefficient_norm_sq_expand (A : OrthogonalCoefficients) (c : Plane) (x y : ℝ) :
    ‖c + A.toFrame (point x y)‖ ^ 2 =
      c 0 ^ 2 + c 1 ^ 2 +
        2 * x * (c 0 * A.a + c 1 * A.c) +
        2 * y * (c 0 * A.b + c 1 * A.d) + x ^ 2 + y ^ 2 := by
  rw [plane_norm_sq, A.toFrame_apply]
  change (c 0 + (A.a * x + A.b * y)) ^ 2 +
    (c 1 + (A.c * x + A.d * y)) ^ 2 = _
  calc
    _ = c 0 ^ 2 + c 1 ^ 2 + 2 * x * (c 0 * A.a + c 1 * A.c) +
        2 * y * (c 0 * A.b + c 1 * A.d) +
        x ^ 2 * (A.a ^ 2 + A.c ^ 2) + y ^ 2 * (A.b ^ 2 + A.d ^ 2) +
        2 * x * y * (A.a * A.b + A.c * A.d) := by ring
    _ = _ := by rw [A.first_unit, A.second_unit, A.orthogonal]; ring

def FourVertexBounds (r : ℝ≥0) (c : Plane) (A : OrthogonalCoefficients) : Prop :=
  ‖c + A.toFrame (point (-1 / 2) (-1 / 2))‖ ^ 2 ≤ (r : ℝ) ^ 2 ∧
  ‖c + A.toFrame (point (-1 / 2) (1 / 2))‖ ^ 2 ≤ (r : ℝ) ^ 2 ∧
  ‖c + A.toFrame (point (1 / 2) (-1 / 2))‖ ^ 2 ≤ (r : ℝ) ^ 2 ∧
  ‖c + A.toFrame (point (1 / 2) (1 / 2))‖ ^ 2 ≤ (r : ℝ) ^ 2

theorem vertex_bound_max {r : ℝ≥0} {c : Plane} {A : OrthogonalCoefficients}
    (h : FourVertexBounds r c A) :
    c 0 ^ 2 + c 1 ^ 2 + |c 0 * A.a + c 1 * A.c| +
      |c 0 * A.b + c 1 * A.d| + 1 / 2 ≤ (r : ℝ) ^ 2 := by
  obtain ⟨h₀₀, h₀₁, h₁₀, h₁₁⟩ := h
  rw [coefficient_norm_sq_expand] at h₀₀ h₀₁ h₁₀ h₁₁
  by_cases hx : 0 ≤ c 0 * A.a + c 1 * A.c <;>
    by_cases hy : 0 ≤ c 0 * A.b + c 1 * A.d
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]; nlinarith only [h₁₁]
  · rw [abs_of_nonneg hx, abs_of_neg (lt_of_not_ge hy)]; nlinarith only [h₁₀]
  · rw [abs_of_neg (lt_of_not_ge hx), abs_of_nonneg hy]; nlinarith only [h₀₁]
  · rw [abs_of_neg (lt_of_not_ge hx), abs_of_neg (lt_of_not_ge hy)]; nlinarith only [h₀₀]

private theorem interior_linear_bound {x : ℝ} (hx : |x| < 1 / 2) (k : ℝ) :
    2 * x * k ≤ |k| := by
  have h := mul_le_mul_of_nonneg_right (le_of_lt hx) (abs_nonneg k)
  rw [← abs_mul] at h
  linarith [le_abs_self (x * k)]

theorem inside_of_four_vertex_bounds {r : ℝ≥0} {c : Plane} {A : OrthogonalCoefficients}
    (h : FourVertexBounds r c A) : placedSquare c A.toFrame ⊆ Circle r := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨hx₀, hx₁, hy₀, hy₁⟩ := (mem_centeredSquare_iff p).mp hp
  have hx : |p 0| < 1 / 2 := abs_lt.mpr ⟨hx₀, hx₁⟩
  have hy : |p 1| < 1 / 2 := abs_lt.mpr ⟨hy₀, hy₁⟩
  have hx2 : (p 0) ^ 2 < 1 / 4 := by
    nlinarith [mul_pos (by linarith : 0 < p 0 + 1 / 2)
      (by linarith : 0 < 1 / 2 - p 0)]
  have hy2 : (p 1) ^ 2 < 1 / 4 := by
    nlinarith [mul_pos (by linarith : 0 < p 1 + 1 / 2)
      (by linarith : 0 < 1 / 2 - p 1)]
  have hpoint : p = point (p 0) (p 1) := by
    ext k; fin_cases k <;> rfl
  apply (mem_circle_iff_norm_sq _ _).mpr
  rw [hpoint, coefficient_norm_sq_expand]
  have hxlin := interior_linear_bound hx (c 0 * A.a + c 1 * A.c)
  have hylin := interior_linear_bound hy (c 0 * A.b + c 1 * A.d)
  have hmax := vertex_bound_max h
  nlinarith only [hx2, hy2, hxlin, hylin, hmax]

theorem inside_iff_four_vertex_bounds (r : ℝ≥0) (c : Plane) (A : OrthogonalCoefficients) :
    placedSquare c A.toFrame ⊆ Circle r ↔ FourVertexBounds r c A :=
  ⟨rotated_four_vertex_bounds, inside_of_four_vertex_bounds⟩

end ThreeSquares
