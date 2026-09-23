import ThreeSquares.FrameCoordinates
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # A packing model with finitely many real parameters

The four entries of each orthogonal matrix replace an arbitrary isometry.
The converse construction proves that this is an exact model, not a relaxation.
Both determinant signs are retained.
-/

open scoped NNReal
open SquarePacking

noncomputable section

namespace ThreeSquares

structure OrthogonalCoefficients where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  first_unit : a ^ 2 + c ^ 2 = 1
  second_unit : b ^ 2 + d ^ 2 = 1
  orthogonal : a * b + c * d = 0

def frameCoefficients (L : Plane ≃ₗᵢ[ℝ] Plane) : OrthogonalCoefficients where
  a := L (point 1 0) 0
  b := L (point 0 1) 0
  c := L (point 1 0) 1
  d := L (point 0 1) 1
  first_unit := frame_first_column_unit L
  second_unit := frame_second_column_unit L
  orthogonal := frame_columns_orthogonal L

def OrthogonalCoefficients.linearMap (A : OrthogonalCoefficients) : Plane →ₗ[ℝ] Plane where
  toFun p := point (A.a * p 0 + A.b * p 1) (A.c * p 0 + A.d * p 1)
  map_add' p q := by
    ext k
    fin_cases k <;> simp [point] <;> ring
  map_smul' t p := by
    ext k
    fin_cases k <;> simp [point] <;> ring

theorem OrthogonalCoefficients.linearMap_norm (A : OrthogonalCoefficients) (p : Plane) :
    ‖A.linearMap p‖ = ‖p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [plane_norm_sq, plane_norm_sq]
  change (A.a * p 0 + A.b * p 1) ^ 2 + (A.c * p 0 + A.d * p 1) ^ 2 = _
  calc
    _ = (A.a ^ 2 + A.c ^ 2) * p 0 ^ 2 + (A.b ^ 2 + A.d ^ 2) * p 1 ^ 2 +
        2 * (A.a * A.b + A.c * A.d) * p 0 * p 1 := by ring
    _ = p 0 ^ 2 + p 1 ^ 2 := by rw [A.first_unit, A.second_unit, A.orthogonal]; ring

def OrthogonalCoefficients.toFrame (A : OrthogonalCoefficients) : Plane ≃ₗᵢ[ℝ] Plane :=
  (show Plane →ₗᵢ[ℝ] Plane from
    { A.linearMap with norm_map' := A.linearMap_norm }).toLinearIsometryEquiv rfl

@[simp] theorem OrthogonalCoefficients.toFrame_apply (A : OrthogonalCoefficients) (p : Plane) :
    A.toFrame p = point (A.a * p 0 + A.b * p 1) (A.c * p 0 + A.d * p 1) := rfl

theorem frameCoefficients_toFrame (L : Plane ≃ₗᵢ[ℝ] Plane) :
    (frameCoefficients L).toFrame = L := by
  ext p k
  rw [OrthogonalCoefficients.toFrame_apply]
  fin_cases k
  · change L (point 1 0) 0 * p 0 + L (point 0 1) 0 * p 1 = L p 0
    rw [frame_apply_coordinates L p 0]
    ring
  · change L (point 1 0) 1 * p 0 + L (point 0 1) 1 * p 1 = L p 1
    rw [frame_apply_coordinates L p 1]
    ring

structure CoefficientPacking (n : ℕ) (r : ℝ≥0) where
  centers : Fin n → Plane
  coefficients : Fin n → OrthogonalCoefficients
  disjoint : Pairwise fun i j => Disjoint
    (placedSquare (centers i) (coefficients i).toFrame)
    (placedSquare (centers j) (coefficients j).toFrame)
  inside : ∀ i, placedSquare (centers i) (coefficients i).toFrame ⊆ Circle r

def CoefficientPacking.toFramed {n : ℕ} {r : ℝ≥0} (P : CoefficientPacking n r) :
    FramedPacking n r where
  centers := P.centers
  frames i := (P.coefficients i).toFrame
  disjoint := P.disjoint
  inside := P.inside

def FramedPacking.toCoefficients {n : ℕ} {r : ℝ≥0} (P : FramedPacking n r) :
    CoefficientPacking n r where
  centers := P.centers
  coefficients i := frameCoefficients (P.frames i)
  disjoint := by simpa only [frameCoefficients_toFrame] using P.disjoint
  inside := by simpa only [frameCoefficients_toFrame] using P.inside

theorem coefficient_packing_iff (n : ℕ) (r : ℝ≥0) :
    Nonempty (CoefficientPacking n r) ↔ Nonempty (Packing n UnitSquare (Circle r)) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.toFramed.toPacking⟩
  · rintro ⟨P⟩
    exact ⟨(toFramedPacking P).toCoefficients⟩

def identityCoefficients : OrthogonalCoefficients where
  a := 1
  b := 0
  c := 0
  d := 1
  first_unit := by norm_num
  second_unit := by norm_num
  orthogonal := by norm_num

theorem frameCoefficients_refl :
    frameCoefficients (LinearIsometryEquiv.refl ℝ Plane) = identityCoefficients := rfl

theorem normalized_coefficient_packing_iff (n : ℕ) (r : ℝ≥0) (i : Fin n) :
    (∃ P : CoefficientPacking n r, P.coefficients i = identityCoefficients) ↔
      Nonempty (Packing n UnitSquare (Circle r)) := by
  constructor
  · rintro ⟨P, _⟩
    exact ⟨P.toFramed.toPacking⟩
  · intro h
    obtain ⟨P, hP⟩ := (normalized_packing_iff n r i).mpr h
    refine ⟨P.toCoefficients, ?_⟩
    change frameCoefficients (P.frames i) = identityCoefficients
    rw [hP, frameCoefficients_refl]

end ThreeSquares
