import ThreeSquares.AxisAligned
import Mathlib.Tactic.FunProp

/-! # From open-square containment to closed vertex inequalities -/

open scoped NNReal
open SquarePacking Set

noncomputable section

namespace ThreeSquares

def centerEmbedding (x y : ℝ) : Plane ≃ᵢ Plane :=
  IsometryEquiv.vaddConst (point (x - 1 / 2) (y - 1 / 2))

@[simp] theorem centerEmbedding_zero (x y : ℝ) (p : Plane) :
    centerEmbedding x y p 0 = p 0 + (x - 1 / 2) := rfl

@[simp] theorem centerEmbedding_one (x y : ℝ) (p : Plane) :
    centerEmbedding x y p 1 = p 1 + (y - 1 / 2) := rfl

private theorem le_on_closed_interval {f : ℝ → ℝ} {a b C : ℝ}
    (hf : Continuous f) (hab : a < b) (h : ∀ x ∈ Ioo a b, f x ≤ C) :
    ∀ x ∈ Icc a b, f x ≤ C := by
  have hc : IsClosed {x : ℝ | f x ≤ C} := isClosed_le hf continuous_const
  have hs : Ioo a b ⊆ {x : ℝ | f x ≤ C} := h
  have hh := closure_minimal hs hc
  rw [closure_Ioo (ne_of_lt hab)] at hh
  exact hh

/-- Boundary vertex inequalities follow from containment of the open square.
No vertex of the open square is incorrectly assumed to belong to it. -/
theorem vertexBounds_of_inside {r : ℝ≥0} {x y : ℝ}
    (hinside : centerEmbedding x y '' UnitSquare ⊆ Circle r) :
    VertexBounds r x y := by
  have h₀ : ∀ u ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) 1,
      (u + (x - 1 / 2)) ^ 2 + (v + (y - 1 / 2)) ^ 2 ≤ (r : ℝ) ^ 2 := by
    intro u hu v hv
    have hp : point u v ∈ UnitSquare := ⟨hu.1, hu.2, hv.1, hv.2⟩
    have hmem := hinside (mem_image_of_mem (centerEmbedding x y) hp)
    exact le_of_lt hmem
  have h₁ : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) 1,
      (u + (x - 1 / 2)) ^ 2 + (v + (y - 1 / 2)) ^ 2 ≤ (r : ℝ) ^ 2 := by
    intro u hu v hv
    exact le_on_closed_interval (by fun_prop) (by norm_num)
      (fun z hz => h₀ z hz v hv) u hu
  have h₂ : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      (u + (x - 1 / 2)) ^ 2 + (v + (y - 1 / 2)) ^ 2 ≤ (r : ℝ) ^ 2 := by
    intro u hu
    exact le_on_closed_interval (by fun_prop) (by norm_num) (h₁ u hu)
  have h00 := h₂ 0 (by norm_num) 0 (by norm_num)
  have h01 := h₂ 0 (by norm_num) 1 (by norm_num)
  have h10 := h₂ 1 (by norm_num) 0 (by norm_num)
  have h11 := h₂ 1 (by norm_num) 1 (by norm_num)
  constructor <;> nlinarith only [h00, h01, h10, h11]

theorem translated_T_lower_bound {r : ℝ≥0} {a b c d e f : ℝ}
    (ha : centerEmbedding a b '' UnitSquare ⊆ Circle r)
    (hb : centerEmbedding c d '' UnitSquare ⊆ Circle r)
    (hc : centerEmbedding e f '' UnitSquare ⊆ Circle r)
    (hab : 1 ≤ c - a) (hac : 1 ≤ e - a) (hbc : 1 ≤ f - d) :
    radius ≤ r :=
  axis_T_lower_bound (vertexBounds_of_inside ha) (vertexBounds_of_inside hb)
    (vertexBounds_of_inside hc) hab hac hbc

end ThreeSquares
