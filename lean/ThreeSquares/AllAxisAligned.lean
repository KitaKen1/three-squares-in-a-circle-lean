import ThreeSquares.Containment

/-! # The exact lower bound for all axis-aligned configurations

The finite case split has 64 branches: each of the three pairs is separated
left/right or up/down. Every branch uses either a span of three unit lengths,
or the weighted T-shaped certificate after exchanging/reflection of axes.
This does not permit independent rotations of the squares.
-/

open scoped NNReal
open SquarePacking Set

noncomputable section

namespace ThreeSquares

theorem VertexBounds.swap {r x y : ℝ} (h : VertexBounds r x y) :
    VertexBounds r y x := by
  constructor <;> nlinarith only [h.leftDown, h.leftUp, h.rightDown, h.rightUp]

theorem VertexBounds.negX {r x y : ℝ} (h : VertexBounds r x y) :
    VertexBounds r (-x) y := by
  constructor <;> nlinarith only [h.leftDown, h.leftUp, h.rightDown, h.rightUp]

def AxisSeparated (a b c d : ℝ) : Prop :=
  1 ≤ c - a ∨ 1 ≤ a - c ∨ 1 ≤ d - b ∨ 1 ≤ b - d

theorem VertexBounds.coordinate_bounds {r x y : ℝ} (hr : 0 ≤ r)
    (h : VertexBounds r x y) :
    -r + 1 / 2 ≤ x ∧ x ≤ r - 1 / 2 ∧ -r + 1 / 2 ≤ y ∧ y ≤ r - 1 / 2 := by
  have hxl : (x - 1 / 2) ^ 2 ≤ r ^ 2 := by
    nlinarith only [h.leftDown, sq_nonneg (y - 1 / 2)]
  have hxu : (x + 1 / 2) ^ 2 ≤ r ^ 2 := by
    nlinarith only [h.rightUp, sq_nonneg (y + 1 / 2)]
  have hyl : (y - 1 / 2) ^ 2 ≤ r ^ 2 := by
    nlinarith only [h.leftDown, sq_nonneg (x - 1 / 2)]
  have hyu : (y + 1 / 2) ^ 2 ≤ r ^ 2 := by
    nlinarith only [h.rightUp, sq_nonneg (x + 1 / 2)]
  have h₁ := (abs_le_of_sq_le_sq' hxl hr).1
  have h₂ := (abs_le_of_sq_le_sq' hxu hr).2
  have h₃ := (abs_le_of_sq_le_sq' hyl hr).1
  have h₄ := (abs_le_of_sq_le_sq' hyu hr).2
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

set_option maxHeartbeats 800000 in
/-- All 64 separation choices are covered by checked proof terms. -/
theorem all_axis_aligned_squared_bound {r a b c d e f : ℝ}
    (hr : 0 ≤ r) (ha : VertexBounds r a b) (hb : VertexBounds r c d)
    (hc : VertexBounds r e f) (hab : AxisSeparated a b c d)
    (hac : AxisSeparated a b e f) (hbc : AxisSeparated c d e f) :
    425 / 256 ≤ r ^ 2 := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄⟩ := ha.coordinate_bounds hr
  obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := hb.coordinate_bounds hr
  obtain ⟨hc₁, hc₂, hc₃, hc₄⟩ := hc.coordinate_bounds hr
  rcases hab with hab | hab | hab | hab <;>
    rcases hac with hac | hac | hac | hac <;>
    rcases hbc with hbc | hbc | hbc | hbc
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · exact axis_T_squared_lower_bound ha hb hc
      (by linarith) (by linarith) (by linarith)
  · exact axis_T_squared_lower_bound ha hc hb
      (by linarith) (by linarith) (by linarith)
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · exact axis_T_squared_lower_bound hb.negX ha.negX hc.negX
      (by linarith) (by linarith) (by linarith)
  · exact axis_T_squared_lower_bound hc.swap.negX ha.swap.negX hb.swap.negX
      (by linarith) (by linarith) (by linarith)
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · exact axis_T_squared_lower_bound hb.negX hc.negX ha.negX
      (by linarith) (by linarith) (by linarith)
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · exact axis_T_squared_lower_bound hc.swap ha.swap hb.swap
      (by linarith) (by linarith) (by linarith)
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · exact axis_T_squared_lower_bound ha.negX hb.negX hc.negX
      (by linarith) (by linarith) (by linarith)
  · exact axis_T_squared_lower_bound ha.negX hc.negX hb.negX
      (by linarith) (by linarith) (by linarith)
  · exact axis_T_squared_lower_bound hb ha hc
      (by linarith) (by linarith) (by linarith)
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · exact axis_T_squared_lower_bound hc.swap.negX hb.swap.negX ha.swap.negX
      (by linarith) (by linarith) (by linarith)
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · exact axis_T_squared_lower_bound hb hc ha
      (by linarith) (by linarith) (by linarith)
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · exact axis_T_squared_lower_bound hc.swap hb.swap ha.swap
      (by linarith) (by linarith) (by linarith)
  · exact axis_T_squared_lower_bound hc.negX ha.negX hb.negX
      (by linarith) (by linarith) (by linarith)
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · exact axis_T_squared_lower_bound hb.swap.negX ha.swap.negX hc.swap.negX
      (by linarith) (by linarith) (by linarith)
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · exact axis_T_squared_lower_bound hc ha hb
      (by linarith) (by linarith) (by linarith)
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · exact axis_T_squared_lower_bound hb.swap.negX hc.swap.negX ha.swap.negX
      (by linarith) (by linarith) (by linarith)
  · exact axis_T_squared_lower_bound ha.swap hb.swap hc.swap
      (by linarith) (by linarith) (by linarith)
  · exact axis_T_squared_lower_bound ha.swap hc.swap hb.swap
      (by linarith) (by linarith) (by linarith)
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · exact axis_T_squared_lower_bound hc.negX hb.negX ha.negX
      (by linarith) (by linarith) (by linarith)
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · exact axis_T_squared_lower_bound hb.swap ha.swap hc.swap
      (by linarith) (by linarith) (by linarith)
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · exact axis_T_squared_lower_bound hc hb ha
      (by linarith) (by linarith) (by linarith)
  · exact axis_T_squared_lower_bound hb.swap hc.swap ha.swap
      (by linarith) (by linarith) (by linarith)
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · exact axis_T_squared_lower_bound ha.swap.negX hb.swap.negX hc.swap.negX
      (by linarith) (by linarith) (by linarith)
  · exact axis_T_squared_lower_bound ha.swap.negX hc.swap.negX hb.swap.negX
      (by linarith) (by linarith) (by linarith)
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]
  · have hspan : (3 / 2 : ℝ) ≤ r := by linarith
    nlinarith [sq_nonneg (r - 3 / 2)]

/-- Disjoint translated open squares must separate in at least one coordinate. -/
theorem axisSeparated_of_disjoint {a b c d : ℝ}
    (h : Disjoint (centerEmbedding a b '' UnitSquare) (centerEmbedding c d '' UnitSquare)) :
    AxisSeparated a b c d := by
  by_contra hn
  simp only [AxisSeparated, not_or, not_le] at hn
  rcases hn with ⟨h₁, h₂, h₃, h₄⟩
  have hm₁ : point ((a + c) / 2) ((b + d) / 2) ∈ centerEmbedding a b '' UnitSquare := by
    refine ⟨point ((c - a) / 2 + 1 / 2) ((d - b) / 2 + 1 / 2), ?_, ?_⟩
    · change 0 < (c - a) / 2 + 1 / 2 ∧ (c - a) / 2 + 1 / 2 < 1 ∧
        0 < (d - b) / 2 + 1 / 2 ∧ (d - b) / 2 + 1 / 2 < 1
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · ext k
      fin_cases k <;>
        simp [centerEmbedding, point, IsometryEquiv.vaddConst] <;> ring
  have hm₂ : point ((a + c) / 2) ((b + d) / 2) ∈ centerEmbedding c d '' UnitSquare := by
    refine ⟨point ((a - c) / 2 + 1 / 2) ((b - d) / 2 + 1 / 2), ?_, ?_⟩
    · change 0 < (a - c) / 2 + 1 / 2 ∧ (a - c) / 2 + 1 / 2 < 1 ∧
        0 < (b - d) / 2 + 1 / 2 ∧ (b - d) / 2 + 1 / 2 < 1
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · ext k
      fin_cases k <;>
        simp [centerEmbedding, point, IsometryEquiv.vaddConst] <;> ring
  exact Set.disjoint_left.mp h hm₁ hm₂

/-- Radii feasible using only translations, without independent square rotations. -/
def axisAlignedFeasibleRadii : Set ℝ≥0 := {r | ∃ x y : Fin 3 → ℝ,
  (Pairwise fun i j => Disjoint (centerEmbedding (x i) (y i) '' UnitSquare)
    (centerEmbedding (x j) (y j) '' UnitSquare)) ∧
  ∀ i, centerEmbedding (x i) (y i) '' UnitSquare ⊆ Circle r}

theorem axis_aligned_lower_bound {r : ℝ≥0} (h : r ∈ axisAlignedFeasibleRadii) :
    radius ≤ r := by
  rcases h with ⟨x, y, hdisjoint, hinside⟩
  have hv₀ := vertexBounds_of_inside (hinside 0)
  have hv₁ := vertexBounds_of_inside (hinside 1)
  have hv₂ := vertexBounds_of_inside (hinside 2)
  have h₀₁ := axisSeparated_of_disjoint (hdisjoint (by decide : (0 : Fin 3) ≠ 1))
  have h₀₂ := axisSeparated_of_disjoint (hdisjoint (by decide : (0 : Fin 3) ≠ 2))
  have h₁₂ := axisSeparated_of_disjoint (hdisjoint (by decide : (1 : Fin 3) ≠ 2))
  have hs := all_axis_aligned_squared_bound r.coe_nonneg hv₀ hv₁ hv₂ h₀₁ h₀₂ h₁₂
  change (radius : ℝ) ≤ r
  apply le_of_sq_le_sq _ r.coe_nonneg
  simpa only [radius_sq_real] using hs

theorem radius_axis_aligned_feasible : radius ∈ axisAlignedFeasibleRadii := by
  let x : Fin 3 → ℝ := ![-11 / 16, 5 / 16, 5 / 16]
  let y : Fin 3 → ℝ := ![0, -1 / 2, 1 / 2]
  have he : ∀ i : Fin 3, centerEmbedding (x i) (y i) = embedding i := by
    intro i
    apply IsometryEquiv.ext
    intro p
    ext k
    fin_cases i <;> fin_cases k <;>
      norm_num [x, y, centerEmbedding, embedding, offset, point, IsometryEquiv.vaddConst]
  refine ⟨x, y, ?_, ?_⟩
  · simpa only [he] using embedding_disjoint
  · intro i
    rw [he]
    exact embedding_inside i

/-- The exact minimum for the restricted, axis-aligned problem. -/
theorem least_axis_aligned_radius : IsLeast axisAlignedFeasibleRadii radius :=
  ⟨radius_axis_aligned_feasible, fun _ hr => axis_aligned_lower_bound hr⟩

end ThreeSquares
