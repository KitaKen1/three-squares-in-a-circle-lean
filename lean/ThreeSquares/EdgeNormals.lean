import ThreeSquares.PiecewiseLinear

/-! # The four separating axes of two squares

A separating linear functional can be chosen perpendicular to an edge of
one of the squares. Boundary contact is included throughout.
-/

noncomputable section

namespace ThreeSquares

/-- Coordinate along an axis of a square's orthonormal frame. -/
def frameForm (L : Plane ≃ₗᵢ[ℝ] Plane) (k : Fin 2) : Plane →ₗ[ℝ] ℝ :=
  (coordinateForm k).comp L.symm.toLinearEquiv.toLinearMap

@[simp] theorem frameForm_apply_frame (L : Plane ≃ₗᵢ[ℝ] Plane) (k : Fin 2) (p : Plane) :
    frameForm L k (L p) = p k := by
  change (L.symm (L p)) k = p k
  rw [L.symm_apply_apply]

theorem linear_form_frame_representation (f : Plane →ₗ[ℝ] ℝ)
    (L : Plane ≃ₗᵢ[ℝ] Plane) :
    f = f (L (point 1 0)) • frameForm L 0 + f (L (point 0 1)) • frameForm L 1 := by
  ext p
  have h := linear_form_frame_apply f L (L.symm p)
  simp only [L.apply_symm_apply] at h
  change f p = f (L (point 1 0)) * L.symm p 0 + f (L (point 0 1)) * L.symm p 1
  nlinarith only [h]

/-- A separating functional can be moved to a direction perpendicular to one
of the four edge directions, without losing a non-strict separation. -/
theorem exists_edge_normal_separator {c d : Plane} {L M : Plane ≃ₗᵢ[ℝ] Plane}
    (hdisj : Disjoint (placedSquare c L) (placedSquare d M)) :
    ∃ f : Plane →ₗ[ℝ] ℝ, f ≠ 0 ∧
      projectionRadius L f + projectionRadius M f ≤ f d - f c ∧
      (f (L (point 1 0)) = 0 ∨ f (L (point 0 1)) = 0 ∨
        f (M (point 1 0)) = 0 ∨ f (M (point 0 1)) = 0) := by
  obtain ⟨f, hf, hsep⟩ := exists_separating_projection hdisj
  by_cases ha : f (L (point 1 0)) = 0
  · exact ⟨f, hf, hsep, Or.inl ha⟩
  by_cases hb : f (L (point 0 1)) = 0
  · exact ⟨f, hf, hsep, Or.inr (Or.inl hb)⟩
  let a := f (L (point 1 0))
  let b := f (L (point 0 1))
  let f₀ := a • frameForm L 0
  let f₁ := b • frameForm L 1
  let g (t : ℝ) : Plane →ₗ[ℝ] ℝ := (1 - t) • f₀ + t • f₁
  have hg (t : ℝ) (p : Plane) : g t p = (f₁ p - f₀ p) * t + f₀ p := by
    change (1 - t) * f₀ p + t * f₁ p = _
    ring
  have hg0 (t : ℝ) : g t (L (point 1 0)) = (1 - t) * a := by
    simp [g, f₀, f₁]
  have hg1 (t : ℝ) : g t (L (point 0 1)) = t * b := by
    simp [g, f₀, f₁]
  have hhalf : g (1 / 2) = (1 / 2 : ℝ) • f := by
    have hrep : f = f₀ + f₁ := linear_form_frame_representation f L
    rw [hrep]
    ext p
    change (1 - 1 / 2 : ℝ) * f₀ p + (1 / 2 : ℝ) * f₁ p =
      (1 / 2 : ℝ) * (f₀ p + f₁ p)
    ring
  let A := f₁ (M (point 1 0)) - f₀ (M (point 1 0))
  let B := f₀ (M (point 1 0))
  let C := f₁ (M (point 0 1)) - f₀ (M (point 0 1))
  let D := f₀ (M (point 0 1))
  let m := 2 * ((f₁ d - f₀ d) - (f₁ c - f₀ c)) + |a| - |b|
  let k := 2 * (f₀ d - f₀ c) - |a|
  have hvalue (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
      2 * (g t d - g t c - projectionRadius L (g t) - projectionRadius M (g t)) =
        m * t + k - |A * t + B| - |C * t + D| := by
    unfold projectionRadius
    rw [hg0, hg1, abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - t),
      abs_of_nonneg ht.1, hg t (M (point 1 0)), hg t (M (point 0 1)), hg t d, hg t c]
    dsimp [m, k, A, B, C, D]
    ring
  have hstart : 0 ≤ m * (1 / 2) + k - |A * (1 / 2) + B| - |C * (1 / 2) + D| := by
    rw [← hvalue (1 / 2) (by norm_num), hhalf, projectionRadius_smul,
      projectionRadius_smul]
    norm_num
    linarith
  obtain ⟨t, ht, hbest, hboundary⟩ := exists_endpoint_or_kink A B C D m k (1 / 2) (by norm_num)
  refine ⟨g t, ?_, ?_, ?_⟩
  · intro hz
    have h0 := congrArg (fun q : Plane →ₗ[ℝ] ℝ => q (L (point 1 0))) hz
    have h1 := congrArg (fun q : Plane →ₗ[ℝ] ℝ => q (L (point 0 1))) hz
    simp only [hg0, hg1, LinearMap.zero_apply] at h0 h1
    have ht0 : t = 0 := (mul_eq_zero.mp h1).resolve_right hb
    simp [ht0] at h0
    exact ha h0
  · have := hvalue t ht
    linarith
  · rcases hboundary with h | h | h | h
    · right; left
      rw [hg1, h, zero_mul]
    · left
      rw [hg0, h, sub_self, zero_mul]
    · right; right; left
      exact (hg t (M (point 1 0))).trans h
    · right; right; right
      exact (hg t (M (point 0 1))).trans h

theorem frameForm_ne_zero (L : Plane ≃ₗᵢ[ℝ] Plane) (k : Fin 2) : frameForm L k ≠ 0 := by
  intro h
  fin_cases k
  · have := congrArg (fun q : Plane →ₗ[ℝ] ℝ => q (L (point 1 0))) h
    simp at this
  · have := congrArg (fun q : Plane →ₗ[ℝ] ℝ => q (L (point 0 1))) h
    simp at this

def AxisSeparates (c d : Plane) (L M : Plane ≃ₗᵢ[ℝ] Plane)
    (f : Plane →ₗ[ℝ] ℝ) : Prop :=
  projectionRadius L f + projectionRadius M f ≤ |f d - f c|

private theorem axis_separates_of_multiple {c d : Plane} {L M : Plane ≃ₗᵢ[ℝ] Plane}
    {f g : Plane →ₗ[ℝ] ℝ} {t : ℝ} (hf : f ≠ 0)
    (hsep : projectionRadius L f + projectionRadius M f ≤ f d - f c)
    (heq : f = t • g) : AxisSeparates c d L M g := by
  have ht : t ≠ 0 := by
    intro h
    apply hf
    simp [heq, h]
  rw [heq, projectionRadius_smul, projectionRadius_smul] at hsep
  change |t| * projectionRadius L g + |t| * projectionRadius M g ≤ t * g d - t * g c at hsep
  have hbound : t * (g d - g c) ≤ |t| * |g d - g c| := by
    simpa only [abs_mul] using le_abs_self (t * (g d - g c))
  unfold AxisSeparates
  exact (mul_le_mul_iff_right₀ (abs_pos.mpr ht)).mp (by nlinarith only [hsep, hbound])

theorem disjoint_of_axis_separates {c d : Plane} {L M : Plane ≃ₗᵢ[ℝ] Plane}
    {f : Plane →ₗ[ℝ] ℝ} (hf : f ≠ 0) (hsep : AxisSeparates c d L M f) :
    Disjoint (placedSquare c L) (placedSquare d M) := by
  unfold AxisSeparates at hsep
  by_cases hgap : 0 ≤ f d - f c
  · rw [abs_of_nonneg hgap] at hsep
    exact disjoint_of_projection_separated hf hsep
  · have hneg : (-1 : ℝ) • f ≠ 0 := by simpa using hf
    apply disjoint_of_projection_separated hneg
    rw [projectionRadius_smul, projectionRadius_smul]
    rw [abs_of_neg (lt_of_not_ge hgap)] at hsep
    norm_num
    linarith

/-- The separating-axis theorem for two open squares: exactly four possible
unoriented axes suffice, including cases where their boundaries touch. -/
theorem disjoint_iff_four_axes (c d : Plane) (L M : Plane ≃ₗᵢ[ℝ] Plane) :
    Disjoint (placedSquare c L) (placedSquare d M) ↔
      AxisSeparates c d L M (frameForm L 0) ∨
      AxisSeparates c d L M (frameForm L 1) ∨
      AxisSeparates c d L M (frameForm M 0) ∨
      AxisSeparates c d L M (frameForm M 1) := by
  constructor
  · intro hdisj
    obtain ⟨f, hf, hsep, hzero⟩ := exists_edge_normal_separator hdisj
    have haxis (N : Plane ≃ₗᵢ[ℝ] Plane)
        (h : f (N (point 1 0)) = 0 ∨ f (N (point 0 1)) = 0) :
        AxisSeparates c d L M (frameForm N 0) ∨
        AxisSeparates c d L M (frameForm N 1) := by
      have hrep := linear_form_frame_representation f N
      rcases h with h | h
      · right
        apply axis_separates_of_multiple hf hsep
        simpa [h] using hrep
      · left
        apply axis_separates_of_multiple hf hsep
        simpa [h] using hrep
    rcases hzero with h | h | h | h
    · rcases haxis L (Or.inl h) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases haxis L (Or.inr h) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (haxis M (Or.inl h)))
    · exact Or.inr (Or.inr (haxis M (Or.inr h)))
  · intro h
    rcases h with h | h | h | h
    all_goals exact disjoint_of_axis_separates (frameForm_ne_zero _ _) h

end ThreeSquares
