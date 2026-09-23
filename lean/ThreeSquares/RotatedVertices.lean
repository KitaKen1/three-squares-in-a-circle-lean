import ThreeSquares.FrameCoordinates
import Mathlib.Tactic.FunProp

/-! # Closed vertex bounds for arbitrary rotated or reflected squares

The FC square and circle are open sets. Continuity supplies non-strict bounds
on the closed square; boundary vertices are not treated as interior points.
-/

open scoped NNReal
open SquarePacking Set

noncomputable section

namespace ThreeSquares

private theorem placed_norm_sq_coordinates (c : Plane) (L : Plane ≃ₗᵢ[ℝ] Plane)
    (x y : ℝ) :
    ‖c + L (point x y)‖ ^ 2 =
      (c 0 + (x * L (point 1 0) 0 + y * L (point 0 1) 0)) ^ 2 +
      (c 1 + (x * L (point 1 0) 1 + y * L (point 0 1) 1)) ^ 2 := by
  rw [plane_norm_sq, PiLp.add_apply, PiLp.add_apply,
    frame_apply_coordinates L (point x y) 0,
    frame_apply_coordinates L (point x y) 1]
  rfl

theorem closed_square_norm_bound {r : ℝ≥0} {c : Plane} {L : Plane ≃ₗᵢ[ℝ] Plane}
    (hinside : placedSquare c L ⊆ Circle r)
    {x y : ℝ} (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hy : y ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    ‖c + L (point x y)‖ ^ 2 ≤ (r : ℝ) ^ 2 := by
  let f : ℝ × ℝ → ℝ := fun z =>
    (c 0 + (z.1 * L (point 1 0) 0 + z.2 * L (point 0 1) 0)) ^ 2 +
    (c 1 + (z.1 * L (point 1 0) 1 + z.2 * L (point 0 1) 1)) ^ 2
  have hf : Continuous f := by fun_prop
  have hc : IsClosed {z : ℝ × ℝ | f z ≤ (r : ℝ) ^ 2} :=
    isClosed_le hf continuous_const
  have ho : Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2) ⊆
      {z : ℝ × ℝ | f z ≤ (r : ℝ) ^ 2} := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hp : point u v ∈ CenteredSquare := by
      rw [mem_centeredSquare_iff]
      exact ⟨hu.1, hu.2, hv.1, hv.2⟩
    have hb := le_of_lt ((mem_circle_iff_norm_sq _ _).mp (hinside ⟨point u v, hp, rfl⟩))
    rw [placed_norm_sq_coordinates] at hb
    exact hb
  have hh := closure_minimal ho hc
  have hxy : (x, y) ∈ closure (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    simpa only [closure_prod_eq, closure_Ioo (by norm_num : (-(1 / 2 : ℝ)) ≠ 1 / 2)]
      using (show (x, y) ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        Icc (-(1 / 2 : ℝ)) (1 / 2) from ⟨hx, hy⟩)
  rw [placed_norm_sq_coordinates]
  exact hh hxy

theorem rotated_four_vertex_bounds {r : ℝ≥0} {c : Plane} {L : Plane ≃ₗᵢ[ℝ] Plane}
    (hinside : placedSquare c L ⊆ Circle r) :
    ‖c + L (point (-1 / 2) (-1 / 2))‖ ^ 2 ≤ (r : ℝ) ^ 2 ∧
    ‖c + L (point (-1 / 2) (1 / 2))‖ ^ 2 ≤ (r : ℝ) ^ 2 ∧
    ‖c + L (point (1 / 2) (-1 / 2))‖ ^ 2 ≤ (r : ℝ) ^ 2 ∧
    ‖c + L (point (1 / 2) (1 / 2))‖ ^ 2 ≤ (r : ℝ) ^ 2 := by
  exact ⟨closed_square_norm_bound hinside (by norm_num) (by norm_num),
    closed_square_norm_bound hinside (by norm_num) (by norm_num),
    closed_square_norm_bound hinside (by norm_num) (by norm_num),
    closed_square_norm_bound hinside (by norm_num) (by norm_num)⟩

end ThreeSquares
