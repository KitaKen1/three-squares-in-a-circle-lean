import ThreeSquares.NormalizePacking

/-! # Finite real coordinates for the orthogonal frames

Each frame is determined by four real entries. The two columns have unit
length and are orthogonal; this includes both determinant signs.
-/

noncomputable section

namespace ThreeSquares

theorem point_decomposition (p : Plane) :
    p = p 0 • point 1 0 + p 1 • point 0 1 := by
  ext k
  fin_cases k <;> simp [point]

theorem frame_apply_coordinates (L : Plane ≃ₗᵢ[ℝ] Plane) (p : Plane) (k : Fin 2) :
    L p k = p 0 * L (point 1 0) k + p 1 * L (point 0 1) k := by
  conv_lhs => rw [point_decomposition p]
  simp

theorem frame_first_column_unit (L : Plane ≃ₗᵢ[ℝ] Plane) :
    L (point 1 0) 0 ^ 2 + L (point 1 0) 1 ^ 2 = 1 := by
  rw [← plane_norm_sq, L.norm_map, plane_norm_sq]
  norm_num

theorem frame_second_column_unit (L : Plane ≃ₗᵢ[ℝ] Plane) :
    L (point 0 1) 0 ^ 2 + L (point 0 1) 1 ^ 2 = 1 := by
  rw [← plane_norm_sq, L.norm_map, plane_norm_sq]
  norm_num

theorem frame_columns_orthogonal (L : Plane ≃ₗᵢ[ℝ] Plane) :
    L (point 1 0) 0 * L (point 0 1) 0 +
      L (point 1 0) 1 * L (point 0 1) 1 = 0 := by
  have h₁ := frame_first_column_unit L
  have h₂ := frame_second_column_unit L
  have hsum : (L (point 1 1) 0) ^ 2 + (L (point 1 1) 1) ^ 2 = 2 := by
    rw [← plane_norm_sq, L.norm_map, plane_norm_sq]
    norm_num
  rw [frame_apply_coordinates L (point 1 1) 0,
    frame_apply_coordinates L (point 1 1) 1] at hsum
  norm_num at hsum
  nlinarith

end ThreeSquares
