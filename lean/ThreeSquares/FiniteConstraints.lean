import ThreeSquares.SeparatorCoordinates
import ThreeSquares.VertexContainment

/-! # An exact finite system of real constraints for FC packing

Containment uses four explicit quadratic vertex inequalities per square.
Non-overlap uses one normalized separating direction per unordered pair.
Only finite index quantifiers and real coordinates remain; there is no
quantification over the points of a square in this model.
-/

open scoped NNReal
open SquarePacking

noncomputable section

namespace ThreeSquares

def vertexSquared (c : Plane) (A : OrthogonalCoefficients) (x y : ℝ) : ℝ :=
  (c 0 + (A.a * x + A.b * y)) ^ 2 + (c 1 + (A.c * x + A.d * y)) ^ 2

theorem norm_sq_eq_vertexSquared (c : Plane) (A : OrthogonalCoefficients) (x y : ℝ) :
    ‖c + A.toFrame (point x y)‖ ^ 2 = vertexSquared c A x y := by
  rw [plane_norm_sq, A.toFrame_apply]
  rfl

def VertexInequalities (r : ℝ≥0) (c : Plane) (A : OrthogonalCoefficients) : Prop :=
  vertexSquared c A (-1 / 2) (-1 / 2) ≤ (r : ℝ) ^ 2 ∧
  vertexSquared c A (-1 / 2) (1 / 2) ≤ (r : ℝ) ^ 2 ∧
  vertexSquared c A (1 / 2) (-1 / 2) ≤ (r : ℝ) ^ 2 ∧
  vertexSquared c A (1 / 2) (1 / 2) ≤ (r : ℝ) ^ 2

theorem vertex_inequalities_iff_inside (r : ℝ≥0) (c : Plane)
    (A : OrthogonalCoefficients) :
    VertexInequalities r c A ↔ placedSquare c A.toFrame ⊆ Circle r := by
  rw [inside_iff_four_vertex_bounds]
  simp only [FourVertexBounds, VertexInequalities, norm_sq_eq_vertexSquared]

structure FiniteConstraintPacking (n : ℕ) (r : ℝ≥0) where
  centers : Fin n → Plane
  coefficients : Fin n → OrthogonalCoefficients
  vertices : ∀ i, VertexInequalities r (centers i) (coefficients i)
  separators : ∀ i j, i < j → ∃ u v : ℝ, |u| + |v| = 1 ∧
    SeparatorInequality (centers i) (centers j) (coefficients i) (coefficients j) u v

def FiniteConstraintPacking.toCoefficients {n : ℕ} {r : ℝ≥0}
    (P : FiniteConstraintPacking n r) : CoefficientPacking n r where
  centers := P.centers
  coefficients := P.coefficients
  inside i := (vertex_inequalities_iff_inside _ _ _).mp (P.vertices i)
  disjoint := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact (coefficient_disjoint_iff_separator _ _ _ _).mpr (P.separators i j h)
    · exact ((coefficient_disjoint_iff_separator _ _ _ _).mpr (P.separators j i h)).symm

def CoefficientPacking.toFiniteConstraints {n : ℕ} {r : ℝ≥0}
    (P : CoefficientPacking n r) : FiniteConstraintPacking n r where
  centers := P.centers
  coefficients := P.coefficients
  vertices i := (vertex_inequalities_iff_inside _ _ _).mpr (P.inside i)
  separators i j hij := P.pairwise_separators (i := i) (j := j) (ne_of_lt hij)

theorem finite_constraints_packing_iff (n : ℕ) (r : ℝ≥0) :
    Nonempty (FiniteConstraintPacking n r) ↔ Nonempty (Packing n UnitSquare (Circle r)) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.toCoefficients.toFramed.toPacking⟩
  · rintro ⟨P⟩
    exact ⟨(toFramedPacking P).toCoefficients.toFiniteConstraints⟩

theorem normalized_finite_constraints_packing_iff (n : ℕ) (r : ℝ≥0) (i : Fin n) :
    (∃ P : FiniteConstraintPacking n r, P.coefficients i = identityCoefficients) ↔
      Nonempty (Packing n UnitSquare (Circle r)) := by
  constructor
  · rintro ⟨P, _⟩
    exact ⟨P.toCoefficients.toFramed.toPacking⟩
  · intro h
    obtain ⟨P, hi⟩ := (normalized_coefficient_packing_iff n r i).mpr h
    exact ⟨P.toFiniteConstraints, hi⟩

end ThreeSquares
