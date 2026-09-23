import ThreeSquares.FramedPacking

/-! # Orthogonal normalization of a complete packing

A common orthogonal transformation preserves the origin-centered FC circle and
all non-overlap conditions. The frame of any chosen square can be made the
identity, without excluding reflected placements of the other squares.
-/

open scoped NNReal
open SquarePacking Set

noncomputable section

namespace ThreeSquares

theorem plane_norm_sq (p : Plane) : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
  simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq p

theorem mem_circle_iff_norm_sq (p : Plane) (r : ℝ≥0) :
    p ∈ Circle r ↔ ‖p‖ ^ 2 < (r : ℝ) ^ 2 := by
  change p 0 ^ 2 + p 1 ^ 2 < (r : ℝ) ^ 2 ↔ _
  rw [plane_norm_sq]

theorem linear_circle_iff (Q : Plane ≃ₗᵢ[ℝ] Plane) (p : Plane) (r : ℝ≥0) :
    Q p ∈ Circle r ↔ p ∈ Circle r := by
  simp only [mem_circle_iff_norm_sq, Q.norm_map]

theorem placedSquare_reframe (c : Plane) (L Q : Plane ≃ₗᵢ[ℝ] Plane) :
    placedSquare (Q c) (L.trans Q) = Q '' placedSquare c L := by
  simp only [placedSquare, Set.image_image,
    LinearIsometryEquiv.trans_apply, map_add]

def FramedPacking.reframe {n : ℕ} {r : ℝ≥0} (P : FramedPacking n r)
    (Q : Plane ≃ₗᵢ[ℝ] Plane) : FramedPacking n r where
  centers i := Q (P.centers i)
  frames i := (P.frames i).trans Q
  disjoint := by
    intro i j hij
    rw [placedSquare_reframe, placedSquare_reframe]
    exact disjoint_image_of_injective Q.injective (P.disjoint hij)
  inside := by
    intro i
    rw [placedSquare_reframe]
    rintro _ ⟨q, hq, rfl⟩
    exact (linear_circle_iff Q q r).mpr (P.inside i hq)

def FramedPacking.normalize {n : ℕ} {r : ℝ≥0} (P : FramedPacking n r)
    (i : Fin n) : FramedPacking n r :=
  P.reframe (P.frames i).symm

theorem FramedPacking.normalize_frame {n : ℕ} {r : ℝ≥0}
    (P : FramedPacking n r) (i : Fin n) :
    (P.normalize i).frames i = LinearIsometryEquiv.refl ℝ Plane := by
  exact LinearIsometryEquiv.self_trans_symm _

theorem normalized_packing_iff (n : ℕ) (r : ℝ≥0) (i : Fin n) :
    (∃ P : FramedPacking n r, P.frames i = LinearIsometryEquiv.refl ℝ Plane) ↔
      Nonempty (Packing n UnitSquare (Circle r)) := by
  constructor
  · rintro ⟨P, _⟩
    exact ⟨P.toPacking⟩
  · rintro ⟨P⟩
    exact ⟨(toFramedPacking P).normalize i, FramedPacking.normalize_frame _ _⟩

theorem FramedPacking.center_norm_lt {n : ℕ} {r : ℝ≥0}
    (P : FramedPacking n r) (i : Fin n) : ‖P.centers i‖ < r := by
  have hs := (mem_circle_iff_norm_sq _ _).mp (P.center_inside i)
  nlinarith [norm_nonneg (P.centers i), r.coe_nonneg]

end ThreeSquares
