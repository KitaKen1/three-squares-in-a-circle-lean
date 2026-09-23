import ThreeSquares.FrameCoordinates

/-! # Exact projections of open squares

A nonzero real linear functional maps an open square to an open interval.
Its half-width is the sum of the absolute projections of the two frame
vectors, divided by two. No unit-normal or orientation assumption is needed.
-/

open Set

noncomputable section

namespace ThreeSquares

def projectionRadius (L : Plane ≃ₗᵢ[ℝ] Plane) (f : Plane →ₗ[ℝ] ℝ) : ℝ :=
  (|f (L (point 1 0))| + |f (L (point 0 1))|) / 2

theorem linear_form_frame_apply (f : Plane →ₗ[ℝ] ℝ)
    (L : Plane ≃ₗᵢ[ℝ] Plane) (p : Plane) :
    f (L p) = p 0 * f (L (point 1 0)) + p 1 * f (L (point 0 1)) := by
  conv_lhs => rw [point_decomposition p]
  simp

theorem projectionRadius_nonneg (L : Plane ≃ₗᵢ[ℝ] Plane) (f : Plane →ₗ[ℝ] ℝ) :
    0 ≤ projectionRadius L f := by
  unfold projectionRadius
  positivity

theorem projectionRadius_pos (L : Plane ≃ₗᵢ[ℝ] Plane) {f : Plane →ₗ[ℝ] ℝ}
    (hf : f ≠ 0) : 0 < projectionRadius L f := by
  have hn : f (L (point 1 0)) ≠ 0 ∨ f (L (point 0 1)) ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    ext p
    obtain ⟨q, rfl⟩ := L.surjective p
    rw [linear_form_frame_apply, h.1, h.2]
    simp
  unfold projectionRadius
  rcases hn with h | h
  · have := abs_pos.mpr h
    linarith [abs_nonneg (f (L (point 0 1)))]
  · have := abs_pos.mpr h
    linarith [abs_nonneg (f (L (point 1 0)))]

private theorem abs_linear_lt {a b x y : ℝ}
    (hs : 0 < |a| + |b|) (hx : |x| < 1 / 2) (hy : |y| < 1 / 2) :
    |x * a + y * b| < (|a| + |b|) / 2 := by
  have hm : max |x| |y| < 1 / 2 := max_lt hx hy
  calc
    |x * a + y * b| ≤ |x * a| + |y * b| := abs_add_le _ _
    _ = |x| * |a| + |y| * |b| := by rw [abs_mul, abs_mul]
    _ ≤ max |x| |y| * (|a| + |b|) := by
      nlinarith [mul_le_mul_of_nonneg_right (le_max_left |x| |y|) (abs_nonneg a),
        mul_le_mul_of_nonneg_right (le_max_right |x| |y|) (abs_nonneg b)]
    _ < (|a| + |b|) / 2 := by nlinarith

theorem projection_centered_strict {L : Plane ≃ₗᵢ[ℝ] Plane}
    {f : Plane →ₗ[ℝ] ℝ} (hf : f ≠ 0) {p : Plane} (hp : p ∈ CenteredSquare) :
    |f (L p)| < projectionRadius L f := by
  obtain ⟨hx₀, hx₁, hy₀, hy₁⟩ := (mem_centeredSquare_iff p).mp hp
  have hs := projectionRadius_pos L hf
  unfold projectionRadius at *
  rw [linear_form_frame_apply]
  exact abs_linear_lt (by linarith) (abs_lt.mpr ⟨hx₀, hx₁⟩)
    (abs_lt.mpr ⟨hy₀, hy₁⟩)

theorem projection_placed_strict {c : Plane} {L : Plane ≃ₗᵢ[ℝ] Plane}
    {f : Plane →ₗ[ℝ] ℝ} (hf : f ≠ 0) {p : Plane} (hp : p ∈ placedSquare c L) :
    |f p - f c| < projectionRadius L f := by
  obtain ⟨q, hq, rfl⟩ := hp
  simpa only [map_add, add_sub_cancel_left] using projection_centered_strict hf hq

private theorem linear_value_exists {a b t : ℝ} (hs : 0 < |a| + |b|)
    (ht : |t| < (|a| + |b|) / 2) :
    ∃ x y : ℝ, |x| < 1 / 2 ∧ |y| < 1 / 2 ∧ x * a + y * b = t := by
  let k := t / (|a| + |b|)
  have hk : |k| < 1 / 2 := by
    dsimp [k]
    rw [abs_div, abs_of_pos hs]
    apply (div_lt_iff₀ hs).mpr
    linarith
  have he : k * (|a| + |b|) = t := div_mul_cancel₀ t (ne_of_gt hs)
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · refine ⟨k, k, hk, hk, ?_⟩
    rw [abs_of_nonneg ha, abs_of_nonneg hb] at he
    nlinarith only [he]
  · refine ⟨k, -k, hk, by simpa only [abs_neg] using hk, ?_⟩
    rw [abs_of_nonneg ha, abs_of_neg (lt_of_not_ge hb)] at he
    nlinarith only [he]
  · refine ⟨-k, k, by simpa only [abs_neg] using hk, hk, ?_⟩
    rw [abs_of_neg (lt_of_not_ge ha), abs_of_nonneg hb] at he
    nlinarith only [he]
  · refine ⟨-k, -k, by simpa only [abs_neg] using hk,
      by simpa only [abs_neg] using hk, ?_⟩
    rw [abs_of_neg (lt_of_not_ge ha), abs_of_neg (lt_of_not_ge hb)] at he
    nlinarith only [he]

theorem projection_image_placed (c : Plane) (L : Plane ≃ₗᵢ[ℝ] Plane)
    {f : Plane →ₗ[ℝ] ℝ} (hf : f ≠ 0) :
    f '' placedSquare c L = Ioo (f c - projectionRadius L f)
      (f c + projectionRadius L f) := by
  ext t
  constructor
  · rintro ⟨p, hp, rfl⟩
    have h := abs_lt.mp (projection_placed_strict hf hp)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro ht
    have hs := projectionRadius_pos L hf
    have ht' : |t - f c| < projectionRadius L f :=
      abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨x, y, hx, hy, he⟩ := linear_value_exists
      (show 0 < |f (L (point 1 0))| + |f (L (point 0 1))| by
        unfold projectionRadius at hs; linarith)
      ht'
    refine ⟨c + L (point x y), ⟨point x y, ?_, rfl⟩, ?_⟩
    · rw [mem_centeredSquare_iff]
      exact ⟨(abs_lt.mp hx).1, (abs_lt.mp hx).2, (abs_lt.mp hy).1, (abs_lt.mp hy).2⟩
    · rw [map_add, linear_form_frame_apply]
      change f c + (x * f (L (point 1 0)) + y * f (L (point 0 1))) = t
      linarith

end ThreeSquares
