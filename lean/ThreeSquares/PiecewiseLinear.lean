import ThreeSquares.SeparatorCoordinates

/-! # Moving a feasible direction to an endpoint or a kink

On a closed interval, an affine function minus two absolute values attains
at least its value at any prescribed point at an endpoint or a zero of one
of the two affine expressions. This is the scalar step in the square SAT.
-/

noncomputable section

namespace ThreeSquares

private theorem extreme_boundary (a b c d x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ a * x + b ∧ 0 ≤ c * x + d)
    (hext : (∀ y : ℝ, (0 ≤ y ∧ y ≤ 1 ∧ 0 ≤ a * y + b ∧ 0 ≤ c * y + d) → x ≤ y) ∨
      (∀ y : ℝ, (0 ≤ y ∧ y ≤ 1 ∧ 0 ≤ a * y + b ∧ 0 ≤ c * y + d) → y ≤ x)) :
    x = 0 ∨ x = 1 ∨ a * x + b = 0 ∨ c * x + d = 0 := by
  by_contra hn
  push Not at hn
  have hstrict : 0 < x ∧ x < 1 ∧ 0 < a * x + b ∧ 0 < c * x + d := by
    rcases hx with ⟨h0, h1, h2, h3⟩
    exact ⟨lt_of_le_of_ne h0 (Ne.symm hn.1), lt_of_le_of_ne h1 hn.2.1,
      lt_of_le_of_ne h2 (Ne.symm hn.2.2.1), lt_of_le_of_ne h3 (Ne.symm hn.2.2.2)⟩
  have hopen : IsOpen {y : ℝ | 0 < y ∧ y < 1 ∧ 0 < a * y + b ∧ 0 < c * y + d} :=
    (isOpen_lt continuous_const continuous_id).inter
      ((isOpen_lt continuous_id continuous_const).inter
        ((isOpen_lt continuous_const (show Continuous (fun y : ℝ => a * y + b) by fun_prop)).inter
          (isOpen_lt continuous_const (show Continuous (fun y : ℝ => c * y + d) by fun_prop))))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hstrict
  have hminus : 0 ≤ x - ε / 2 ∧ x - ε / 2 ≤ 1 ∧
      0 ≤ a * (x - ε / 2) + b ∧ 0 ≤ c * (x - ε / 2) + d := by
    have hp : x - ε / 2 ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_of_neg (by linarith)]
      linarith
    exact ⟨(hball hp).1.le, (hball hp).2.1.le,
      (hball hp).2.2.1.le, (hball hp).2.2.2.le⟩
  have hplus : 0 ≤ x + ε / 2 ∧ x + ε / 2 ≤ 1 ∧
      0 ≤ a * (x + ε / 2) + b ∧ 0 ≤ c * (x + ε / 2) + d := by
    have hp : x + ε / 2 ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_of_pos (by linarith)]
      linarith
    exact ⟨(hball hp).1.le, (hball hp).2.1.le,
      (hball hp).2.2.1.le, (hball hp).2.2.2.le⟩
  rcases hext with h | h
  · have := h _ hminus
    linarith
  · have := h _ hplus
    linarith

private theorem linear_region_boundary (a b c d m k t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ a * t + b ∧ 0 ≤ c * t + d) :
    ∃ x : ℝ, (0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ a * x + b ∧ 0 ≤ c * x + d) ∧
      m * t + k ≤ m * x + k ∧
      (x = 0 ∨ x = 1 ∨ a * x + b = 0 ∨ c * x + d = 0) := by
  let S : Set ℝ := {x | 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ a * x + b ∧ 0 ≤ c * x + d}
  have hc : IsCompact S := by
    have hclosed : IsClosed {x : ℝ | 0 ≤ a * x + b ∧ 0 ≤ c * x + d} :=
      (isClosed_le continuous_const (show Continuous (fun x : ℝ => a * x + b) by fun_prop)).inter
        (isClosed_le continuous_const (show Continuous (fun x : ℝ => c * x + d) by fun_prop))
    have heq : S = Set.Icc 0 1 ∩ {x : ℝ | 0 ≤ a * x + b ∧ 0 ≤ c * x + d} := by
      ext x
      simp [S, and_assoc]
    rw [heq]
    exact isCompact_Icc.inter_right hclosed
  have hne : S.Nonempty := ⟨t, ht⟩
  by_cases hm : 0 ≤ m
  · obtain ⟨x, hx, hext⟩ := hc.exists_isMaxOn hne continuous_id.continuousOn
    refine ⟨x, hx, ?_, extreme_boundary a b c d x hx (Or.inr hext)⟩
    have htx : t ≤ x := hext ht
    nlinarith [mul_nonneg hm (sub_nonneg.mpr htx)]
  · obtain ⟨x, hx, hext⟩ := hc.exists_isMinOn hne continuous_id.continuousOn
    refine ⟨x, hx, ?_, extreme_boundary a b c d x hx (Or.inl hext)⟩
    have hxt : x ≤ t := hext ht
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hm)) (sub_nonneg.mpr hxt)]

private theorem abs_eq_signed (s x : ℝ) (hs : s = 1 ∨ s = -1) (hx : 0 ≤ s * x) :
    |x| = s * x := by
  rcases hs with rfl | rfl
  · simpa using abs_of_nonneg (show 0 ≤ x by simpa using hx)
  · have hn : x ≤ 0 := by linarith
    rw [abs_of_nonpos hn]
    ring

/-- A feasible value of an affine expression minus two absolute values can
be preserved at an interval endpoint or at one of the absolute-value kinks. -/
theorem exists_endpoint_or_kink (a b c d m k t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    ∃ x : ℝ, (0 ≤ x ∧ x ≤ 1) ∧
      m * t + k - |a * t + b| - |c * t + d| ≤
        m * x + k - |a * x + b| - |c * x + d| ∧
      (x = 0 ∨ x = 1 ∨ a * x + b = 0 ∨ c * x + d = 0) := by
  have signs (z : ℝ) : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ 0 ≤ s * z := by
    by_cases hz : 0 ≤ z
    · exact ⟨1, Or.inl rfl, by simpa⟩
    · exact ⟨-1, Or.inr rfl, by linarith⟩
  obtain ⟨s, hs, hst⟩ := signs (a * t + b)
  obtain ⟨u, hu, hut⟩ := signs (c * t + d)
  obtain ⟨x, hx, hvalue, hboundary⟩ :=
    linear_region_boundary (s * a) (s * b) (u * c) (u * d)
      (m - s * a - u * c) (k - s * b - u * d) t
      ⟨ht.1, ht.2, by nlinarith only [hst], by nlinarith only [hut]⟩
  have hsx : 0 ≤ s * (a * x + b) := by nlinarith only [hx.2.2.1]
  have hux : 0 ≤ u * (c * x + d) := by nlinarith only [hx.2.2.2]
  refine ⟨x, ⟨hx.1, hx.2.1⟩, ?_, ?_⟩
  · rw [abs_eq_signed s _ hs hst, abs_eq_signed u _ hu hut,
      abs_eq_signed s _ hs hsx, abs_eq_signed u _ hu hux]
    nlinarith only [hvalue]
  · rcases hboundary with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · right; right; left
      rcases hs with rfl | rfl <;> linarith
    · right; right; right
      rcases hu with rfl | rfl <;> linarith

end ThreeSquares
