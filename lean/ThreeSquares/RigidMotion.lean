import ThreeSquares.UpperBound
import Mathlib.Analysis.Normed.Affine.MazurUlam

/-! # Centered coordinates for arbitrary isometric square placements

Mazur-Ulam supplies a linear isometry for every FC isometric equivalence.
Reflections are included. No assumption on the orientation is made.
-/

open scoped NNReal
open SquarePacking Set

noncomputable section

namespace ThreeSquares

def unitCenter : Plane := point (1 / 2) (1 / 2)

def CenteredSquare : Set Plane := {v | v + unitCenter ∈ UnitSquare}

theorem mem_centeredSquare_iff (v : Plane) :
    v ∈ CenteredSquare ↔
      -(1 / 2 : ℝ) < v 0 ∧ v 0 < 1 / 2 ∧ -(1 / 2 : ℝ) < v 1 ∧ v 1 < 1 / 2 := by
  change (0 < v 0 + 1 / 2 ∧ v 0 + 1 / 2 < 1 ∧
    0 < v 1 + 1 / 2 ∧ v 1 + 1 / 2 < 1) ↔ _
  constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;>
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem zero_mem_centeredSquare : (0 : Plane) ∈ CenteredSquare := by
  rw [mem_centeredSquare_iff]
  norm_num

def rigidCenter (f : Plane ≃ᵢ Plane) : Plane := f unitCenter

def rigidLinear (f : Plane ≃ᵢ Plane) : Plane ≃ₗᵢ[ℝ] Plane :=
  f.toRealLinearIsometryEquiv

theorem rigid_apply_centered (f : Plane ≃ᵢ Plane) (p : Plane) :
    f p = rigidCenter f + rigidLinear f (p - unitCenter) := by
  simp only [rigidLinear, map_sub, IsometryEquiv.toRealLinearIsometryEquiv_apply,
    rigidCenter]
  abel

def placedSquare (c : Plane) (L : Plane ≃ₗᵢ[ℝ] Plane) : Set Plane :=
  (fun v => c + L v) '' CenteredSquare

theorem rigid_image_centered (f : Plane ≃ᵢ Plane) :
    f '' UnitSquare = placedSquare (rigidCenter f) (rigidLinear f) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q - unitCenter, ?_, (rigid_apply_centered f q).symm⟩
    change q - unitCenter + unitCenter ∈ UnitSquare
    simpa only [sub_add_cancel] using hq
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v + unitCenter, hv, ?_⟩
    rw [rigid_apply_centered]
    simp only [add_sub_cancel_right]

def frameEmbedding (c : Plane) (L : Plane ≃ₗᵢ[ℝ] Plane) : Plane ≃ᵢ Plane :=
  (IsometryEquiv.addRight (-unitCenter)).trans
    (L.toIsometryEquiv.trans (IsometryEquiv.addRight c))

@[simp] theorem frameEmbedding_apply (c : Plane) (L : Plane ≃ₗᵢ[ℝ] Plane) (p : Plane) :
    frameEmbedding c L p = c + L (p - unitCenter) := by
  simp [frameEmbedding, sub_eq_add_neg, add_comm]

theorem frameEmbedding_image (c : Plane) (L : Plane ≃ₗᵢ[ℝ] Plane) :
    frameEmbedding c L '' UnitSquare = placedSquare c L := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q - unitCenter, ?_, (frameEmbedding_apply c L q).symm⟩
    change q - unitCenter + unitCenter ∈ UnitSquare
    simpa only [sub_add_cancel] using hq
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v + unitCenter, hv, ?_⟩
    simp only [frameEmbedding_apply, add_sub_cancel_right]

theorem center_mem_placedSquare (c : Plane) (L : Plane ≃ₗᵢ[ℝ] Plane) :
    c ∈ placedSquare c L := by
  exact ⟨0, zero_mem_centeredSquare, by simp⟩

end ThreeSquares
