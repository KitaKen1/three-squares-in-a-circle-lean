import ThreeSquares.RigidMotion

/-! # The FC packing problem in center and orthogonal-frame coordinates

Both directions preserve the actual image sets, including their open boundaries.
This representation allows independent rotations and reflections of all squares.
-/

open scoped NNReal
open SquarePacking Set

noncomputable section

namespace ThreeSquares

structure FramedPacking (n : ℕ) (r : ℝ≥0) where
  centers : Fin n → Plane
  frames : Fin n → (Plane ≃ₗᵢ[ℝ] Plane)
  disjoint : Pairwise fun i j => Disjoint (placedSquare (centers i) (frames i))
    (placedSquare (centers j) (frames j))
  inside : ∀ i, placedSquare (centers i) (frames i) ⊆ Circle r

def toFramedPacking {n : ℕ} {r : ℝ≥0} (P : Packing n UnitSquare (Circle r)) :
    FramedPacking n r where
  centers i := rigidCenter (P.embeddings i)
  frames i := rigidLinear (P.embeddings i)
  disjoint := by
    intro i j hij
    simpa only [← rigid_image_centered] using P.disjoint hij
  inside := by
    intro i
    simpa only [← rigid_image_centered] using P.inside i

def FramedPacking.toPacking {n : ℕ} {r : ℝ≥0} (P : FramedPacking n r) :
    Packing n UnitSquare (Circle r) where
  embeddings i := frameEmbedding (P.centers i) (P.frames i)
  disjoint := by
    intro i j hij
    simpa only [frameEmbedding_image] using P.disjoint hij
  inside := by
    intro i
    simpa only [frameEmbedding_image] using P.inside i

theorem framed_packing_iff (n : ℕ) (r : ℝ≥0) :
    Nonempty (FramedPacking n r) ↔ Nonempty (Packing n UnitSquare (Circle r)) :=
  ⟨fun ⟨P⟩ => ⟨P.toPacking⟩, fun ⟨P⟩ => ⟨toFramedPacking P⟩⟩

theorem FramedPacking.center_inside {n : ℕ} {r : ℝ≥0}
    (P : FramedPacking n r) (i : Fin n) : P.centers i ∈ Circle r :=
  P.inside i (center_mem_placedSquare _ _)

end ThreeSquares
