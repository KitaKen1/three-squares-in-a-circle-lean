import ThreeSquares.Separation
import ThreeSquares.FiniteParameters

/-! # Bounded coordinates for separating functionals

Each pair of non-overlapping squares has a separating functional represented
by two real numbers `u, v`, normalized by `|u| + |v| = 1`. This supplies finite
auxiliary variables without yet selecting an edge-normal direction.
-/

noncomputable section

open scoped NNReal

namespace ThreeSquares

def coordinateProjection (u v : ℝ) : Plane →ₗ[ℝ] ℝ where
  toFun p := u * p 0 + v * p 1
  map_add' p q := by change u * (p 0 + q 0) + v * (p 1 + q 1) = _; ring
  map_smul' t p := by change u * (t * p 0) + v * (t * p 1) = t * _; ring

theorem linear_form_coordinate_representation (f : Plane →ₗ[ℝ] ℝ) :
    coordinateProjection (f (point 1 0)) (f (point 0 1)) = f := by
  ext p
  change f (point 1 0) * p 0 + f (point 0 1) * p 1 = f p
  conv_rhs => rw [point_decomposition p]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

theorem projectionRadius_smul (L : Plane ≃ₗᵢ[ℝ] Plane)
    (f : Plane →ₗ[ℝ] ℝ) (t : ℝ) :
    projectionRadius L (t • f) = |t| * projectionRadius L f := by
  simp only [projectionRadius, LinearMap.smul_apply, smul_eq_mul, abs_mul]
  ring

theorem disjoint_iff_normalized_separator (c d : Plane) (L M : Plane ≃ₗᵢ[ℝ] Plane) :
    Disjoint (placedSquare c L) (placedSquare d M) ↔
      ∃ u v : ℝ, |u| + |v| = 1 ∧
        projectionRadius L (coordinateProjection u v) +
          projectionRadius M (coordinateProjection u v) ≤
            u * (d 0 - c 0) + v * (d 1 - c 1) := by
  constructor
  · intro h
    obtain ⟨f, hf, hsep⟩ := exists_separating_projection h
    let s : ℝ := |f (point 1 0)| + |f (point 0 1)|
    have hs : 0 < s := by
      have hp := projectionRadius_pos (LinearIsometryEquiv.refl ℝ Plane) hf
      change 0 < (|f (point 1 0)| + |f (point 0 1)|) / 2 at hp
      dsimp [s]
      linarith
    let g : Plane →ₗ[ℝ] ℝ := s⁻¹ • f
    have hg : |g (point 1 0)| + |g (point 0 1)| = 1 := by
      change |s⁻¹ * f (point 1 0)| + |s⁻¹ * f (point 0 1)| = 1
      rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hs), ← mul_add]
      exact inv_mul_cancel₀ (ne_of_gt hs)
    refine ⟨g (point 1 0), g (point 0 1), hg, ?_⟩
    rw [linear_form_coordinate_representation]
    have hgsep : projectionRadius L g + projectionRadius M g ≤ g d - g c := by
      dsimp [g]
      rw [projectionRadius_smul, projectionRadius_smul, abs_of_pos (inv_pos.mpr hs)]
      change s⁻¹ * projectionRadius L f + s⁻¹ * projectionRadius M f ≤
        s⁻¹ * f d - s⁻¹ * f c
      nlinarith [mul_le_mul_of_nonneg_left hsep (le_of_lt (inv_pos.mpr hs))]
    have he : g d - g c = g (point 1 0) * (d 0 - c 0) +
        g (point 0 1) * (d 1 - c 1) := by
      conv_lhs => rw [← linear_form_coordinate_representation g]
      change _ * d 0 + _ * d 1 - (_ * c 0 + _ * c 1) = _
      ring
    rwa [he] at hgsep
  · rintro ⟨u, v, hn, hsep⟩
    have hf : coordinateProjection u v ≠ 0 := by
      intro hf
      have hu := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f (point 1 0)) hf
      have hv := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f (point 0 1)) hf
      have hu' : u = 0 := by simpa [coordinateProjection] using hu
      have hv' : v = 0 := by simpa [coordinateProjection] using hv
      simp [hu', hv'] at hn
    apply disjoint_of_projection_separated hf
    change _ ≤ (u * d 0 + v * d 1) - (u * c 0 + v * c 1)
    nlinarith only [hsep]

theorem projectionRadius_coefficients (A : OrthogonalCoefficients) (u v : ℝ) :
    projectionRadius A.toFrame (coordinateProjection u v) =
      (|u * A.a + v * A.c| + |u * A.b + v * A.d|) / 2 := by
  simp [projectionRadius, coordinateProjection]

theorem separator_coordinates_bounded {u v : ℝ} (h : |u| + |v| = 1) :
    |u| ≤ 1 ∧ |v| ≤ 1 :=
  ⟨by linarith [abs_nonneg v], by linarith [abs_nonneg u]⟩

def SeparatorInequality (c d : Plane) (A B : OrthogonalCoefficients) (u v : ℝ) : Prop :=
  (|u * A.a + v * A.c| + |u * A.b + v * A.d| +
    |u * B.a + v * B.c| + |u * B.b + v * B.d|) / 2 ≤
      u * (d 0 - c 0) + v * (d 1 - c 1)

theorem coefficient_disjoint_iff_separator (c d : Plane) (A B : OrthogonalCoefficients) :
    Disjoint (placedSquare c A.toFrame) (placedSquare d B.toFrame) ↔
      ∃ u v : ℝ, |u| + |v| = 1 ∧ SeparatorInequality c d A B u v := by
  rw [disjoint_iff_normalized_separator]
  simp only [projectionRadius_coefficients, SeparatorInequality]
  constructor
  · rintro ⟨u, v, hn, h⟩
    exact ⟨u, v, hn, by linarith⟩
  · rintro ⟨u, v, hn, h⟩
    exact ⟨u, v, hn, by linarith⟩

theorem CoefficientPacking.pairwise_separators {n : ℕ} {r : ℝ≥0}
    (P : CoefficientPacking n r) {i j : Fin n} (hij : i ≠ j) :
    ∃ u v : ℝ, |u| + |v| = 1 ∧
      SeparatorInequality (P.centers i) (P.centers j)
        (P.coefficients i) (P.coefficients j) u v :=
  (coefficient_disjoint_iff_separator _ _ _ _).mp (P.disjoint hij)

end ThreeSquares
