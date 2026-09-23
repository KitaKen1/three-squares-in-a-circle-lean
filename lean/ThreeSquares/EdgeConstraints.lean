import ThreeSquares.EdgeNormals
import ThreeSquares.FiniteConstraints

/-! # A finite packing model without auxiliary separating directions

Each unordered pair satisfies a disjunction of four explicit edge-axis
inequalities. Thus the normalized three-square problem uses only the 14
configuration coordinates (with orthogonality equalities), plus the radius.
-/

open scoped NNReal
open SquarePacking

noncomputable section

namespace ThreeSquares

theorem frameForm_coefficients_zero (A : OrthogonalCoefficients) :
    frameForm A.toFrame 0 = coordinateProjection A.a A.c := by
  ext p
  obtain ⟨q, rfl⟩ := A.toFrame.surjective p
  rw [frameForm_apply_frame]
  simp only [coordinateProjection, LinearMap.coe_mk, AddHom.coe_mk, A.toFrame_apply,
    point_zero, point_one]
  linear_combination -(q 0) * A.first_unit - (q 1) * A.orthogonal

theorem frameForm_coefficients_one (A : OrthogonalCoefficients) :
    frameForm A.toFrame 1 = coordinateProjection A.b A.d := by
  ext p
  obtain ⟨q, rfl⟩ := A.toFrame.surjective p
  rw [frameForm_apply_frame]
  simp only [coordinateProjection, LinearMap.coe_mk, AddHom.coe_mk, A.toFrame_apply,
    point_zero, point_one]
  linear_combination -(q 0) * A.orthogonal - (q 1) * A.second_unit

def AxisInequality (c d : Plane) (A B : OrthogonalCoefficients) (u v : ℝ) : Prop :=
  (|u * A.a + v * A.c| + |u * A.b + v * A.d| +
    |u * B.a + v * B.c| + |u * B.b + v * B.d|) / 2 ≤
      |u * (d 0 - c 0) + v * (d 1 - c 1)|

theorem axis_inequality_iff (c d : Plane) (A B : OrthogonalCoefficients) (u v : ℝ) :
    AxisInequality c d A B u v ↔
      AxisSeparates c d A.toFrame B.toFrame (coordinateProjection u v) := by
  unfold AxisInequality AxisSeparates
  rw [projectionRadius_coefficients, projectionRadius_coefficients]
  have h : coordinateProjection u v d - coordinateProjection u v c =
      u * (d 0 - c 0) + v * (d 1 - c 1) := by
    change (u * d 0 + v * d 1) - (u * c 0 + v * c 1) = _
    ring
  rw [h]
  constructor <;> intro h <;> linarith only [h]

def FourAxisSeparation (c d : Plane) (A B : OrthogonalCoefficients) : Prop :=
  AxisInequality c d A B A.a A.c ∨ AxisInequality c d A B A.b A.d ∨
  AxisInequality c d A B B.a B.c ∨ AxisInequality c d A B B.b B.d

theorem coefficient_disjoint_iff_four_axes (c d : Plane) (A B : OrthogonalCoefficients) :
    Disjoint (placedSquare c A.toFrame) (placedSquare d B.toFrame) ↔
      FourAxisSeparation c d A B := by
  rw [disjoint_iff_four_axes]
  simp only [frameForm_coefficients_zero, frameForm_coefficients_one,
    FourAxisSeparation, axis_inequality_iff]

structure EdgeConstraintPacking (n : ℕ) (r : ℝ≥0) where
  centers : Fin n → Plane
  coefficients : Fin n → OrthogonalCoefficients
  vertices : ∀ i, VertexInequalities r (centers i) (coefficients i)
  separations : ∀ i j, i < j → FourAxisSeparation
    (centers i) (centers j) (coefficients i) (coefficients j)

def EdgeConstraintPacking.toCoefficients {n : ℕ} {r : ℝ≥0}
    (P : EdgeConstraintPacking n r) : CoefficientPacking n r where
  centers := P.centers
  coefficients := P.coefficients
  inside i := (vertex_inequalities_iff_inside _ _ _).mp (P.vertices i)
  disjoint := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact (coefficient_disjoint_iff_four_axes _ _ _ _).mpr (P.separations i j h)
    · exact ((coefficient_disjoint_iff_four_axes _ _ _ _).mpr (P.separations j i h)).symm

def CoefficientPacking.toEdgeConstraints {n : ℕ} {r : ℝ≥0}
    (P : CoefficientPacking n r) : EdgeConstraintPacking n r where
  centers := P.centers
  coefficients := P.coefficients
  vertices i := (vertex_inequalities_iff_inside _ _ _).mpr (P.inside i)
  separations i j hij := (coefficient_disjoint_iff_four_axes _ _ _ _).mp
    (P.disjoint (i := i) (j := j) (ne_of_lt hij))

theorem edge_constraints_packing_iff (n : ℕ) (r : ℝ≥0) :
    Nonempty (EdgeConstraintPacking n r) ↔ Nonempty (Packing n UnitSquare (Circle r)) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.toCoefficients.toFramed.toPacking⟩
  · rintro ⟨P⟩
    exact ⟨(toFramedPacking P).toCoefficients.toEdgeConstraints⟩

theorem normalized_edge_constraints_packing_iff (n : ℕ) (r : ℝ≥0) (i : Fin n) :
    (∃ P : EdgeConstraintPacking n r, P.coefficients i = identityCoefficients) ↔
      Nonempty (Packing n UnitSquare (Circle r)) := by
  constructor
  · rintro ⟨P, _⟩
    exact ⟨P.toCoefficients.toFramed.toPacking⟩
  · intro h
    obtain ⟨P, hi⟩ := (normalized_coefficient_packing_iff n r i).mpr h
    exact ⟨P.toEdgeConstraints, hi⟩

end ThreeSquares
