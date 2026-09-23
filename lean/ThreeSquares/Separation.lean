import ThreeSquares.SquareProjection
import Mathlib.Analysis.LocallyConvex.Separation

/-! # Separating functionals for two open squares

Non-overlap is equivalent to separation of their projection intervals along
some nonzero real linear functional. The inequality is non-strict, so boundary
contact is allowed. Reduction to the four edge-normal directions is not yet
part of this module.
-/

open Set

noncomputable section

namespace ThreeSquares

def coordinateForm (k : Fin 2) : Plane →ₗ[ℝ] ℝ where
  toFun p := p k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem centeredSquare_eq_inter : CenteredSquare =
    coordinateForm 0 ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2) ∩
    coordinateForm 1 ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
  ext p
  rw [mem_centeredSquare_iff]
  change (_ ∧ _ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _))
  tauto

theorem convex_centeredSquare : Convex ℝ CenteredSquare := by
  rw [centeredSquare_eq_inter]
  exact ((convex_Ioo _ _).linear_preimage (coordinateForm 0)).inter
    ((convex_Ioo _ _).linear_preimage (coordinateForm 1))

theorem isOpen_centeredSquare : IsOpen CenteredSquare := by
  rw [centeredSquare_eq_inter]
  exact (isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ 0)).inter
    (isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ 1))

theorem convex_placedSquare (c : Plane) (L : Plane ≃ₗᵢ[ℝ] Plane) :
    Convex ℝ (placedSquare c L) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  refine ⟨a • u + b • v, convex_centeredSquare hu hv ha hb hab, ?_⟩
  have hc : a • c + b • c = c := by rw [← add_smul, hab, one_smul]
  change c + L (a • u + b • v) = a • (c + L u) + b • (c + L v)
  rw [map_add, map_smul, map_smul, smul_add, smul_add]
  calc
    c + (a • L u + b • L v) = (a • c + b • c) + (a • L u + b • L v) := by rw [hc]
    _ = _ := by abel

theorem isOpen_placedSquare (c : Plane) (L : Plane ≃ₗᵢ[ℝ] Plane) :
    IsOpen (placedSquare c L) := by
  let h : Plane ≃ₜ Plane := L.toHomeomorph.trans (Homeomorph.addLeft c)
  exact h.isOpenMap _ isOpen_centeredSquare

theorem disjoint_of_projection_separated {c d : Plane}
    {L M : Plane ≃ₗᵢ[ℝ] Plane} {f : Plane →ₗ[ℝ] ℝ} (hf : f ≠ 0)
    (hsep : projectionRadius L f + projectionRadius M f ≤ f d - f c) :
    Disjoint (placedSquare c L) (placedSquare d M) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hp' := abs_lt.mp (projection_placed_strict hf hp)
  have hq' := abs_lt.mp (projection_placed_strict hf hq)
  linarith [hp'.2, hq'.1]

private theorem right_endpoint_le {a b u : ℝ} (hab : a < b)
    (h : Ioo a b ⊆ Iio u) : b ≤ u := by
  have hc := closure_mono h
  rw [closure_Ioo (ne_of_lt hab), closure_Iio] at hc
  exact hc ⟨le_of_lt hab, le_rfl⟩

private theorem le_left_endpoint {a b u : ℝ} (hab : a < b)
    (h : Ioo a b ⊆ Ioi u) : u ≤ a := by
  have hc := closure_mono h
  rw [closure_Ioo (ne_of_lt hab), closure_Ioi] at hc
  exact hc ⟨le_rfl, le_of_lt hab⟩

theorem exists_separating_projection {c d : Plane} {L M : Plane ≃ₗᵢ[ℝ] Plane}
    (hdisj : Disjoint (placedSquare c L) (placedSquare d M)) :
    ∃ f : Plane →ₗ[ℝ] ℝ, f ≠ 0 ∧
      projectionRadius L f + projectionRadius M f ≤ f d - f c := by
  obtain ⟨f, u, hc, hd⟩ := geometric_hahn_banach_open_open
    (convex_placedSquare c L) (isOpen_placedSquare c L)
    (convex_placedSquare d M) (isOpen_placedSquare d M) hdisj
  have hf : f.toLinearMap ≠ 0 := by
    intro hf
    have h₁ := hc c (center_mem_placedSquare c L)
    have h₂ := hd d (center_mem_placedSquare d M)
    have hfc : f c = 0 := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g c) hf
    have hfd : f d = 0 := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g d) hf
    linarith
  have hposL := projectionRadius_pos L hf
  have hposM := projectionRadius_pos M hf
  have hL : f.toLinearMap '' placedSquare c L ⊆ Iio u := by
    rintro _ ⟨p, hp, rfl⟩
    exact hc p hp
  have hM : f.toLinearMap '' placedSquare d M ⊆ Ioi u := by
    rintro _ ⟨p, hp, rfl⟩
    exact hd p hp
  rw [projection_image_placed c L hf] at hL
  rw [projection_image_placed d M hf] at hM
  have h₁ := right_endpoint_le (by linarith :
    f.toLinearMap c - projectionRadius L f.toLinearMap <
      f.toLinearMap c + projectionRadius L f.toLinearMap) hL
  have h₂ := le_left_endpoint (by linarith :
    f.toLinearMap d - projectionRadius M f.toLinearMap <
      f.toLinearMap d + projectionRadius M f.toLinearMap) hM
  exact ⟨f.toLinearMap, hf, by linarith⟩

theorem disjoint_iff_exists_separating_projection (c d : Plane)
    (L M : Plane ≃ₗᵢ[ℝ] Plane) :
    Disjoint (placedSquare c L) (placedSquare d M) ↔
      ∃ f : Plane →ₗ[ℝ] ℝ, f ≠ 0 ∧
        projectionRadius L f + projectionRadius M f ≤ f d - f c :=
  ⟨exists_separating_projection, fun ⟨_, hf, hsep⟩ =>
    disjoint_of_projection_separated hf hsep⟩

end ThreeSquares
