import ThreeSquares.LocalGeometry

/-! # Eliminating reflected frame representatives

Every orthogonal frame in the plane has second column equal to one of the two
quarter turns of its first column.  Reflecting the internal second coordinate
of the centered square does not change the placed set, so every square has an
orientation-preserving representative with only two matrix entries.
-/

open scoped NNReal
open SquarePacking Set

noncomputable section

namespace ThreeSquares

@[ext] theorem OrthogonalCoefficients.ext {A B : OrthogonalCoefficients}
    (ha : A.a = B.a) (hb : A.b = B.b) (hc : A.c = B.c) (hd : A.d = B.d) :
    A = B := by
  cases A
  cases B
  simp_all

/-- Replace an arbitrary orthogonal representative by the positive-determinant
representative having the same first column. -/
def OrthogonalCoefficients.orient (A : OrthogonalCoefficients) :
    OrthogonalCoefficients :=
  rotationCoefficients A.a A.c A.first_unit

@[simp] theorem OrthogonalCoefficients.orient_a (A : OrthogonalCoefficients) :
    A.orient.a = A.a := rfl

@[simp] theorem OrthogonalCoefficients.orient_b (A : OrthogonalCoefficients) :
    A.orient.b = -A.c := rfl

@[simp] theorem OrthogonalCoefficients.orient_c (A : OrthogonalCoefficients) :
    A.orient.c = A.c := rfl

@[simp] theorem OrthogonalCoefficients.orient_d (A : OrthogonalCoefficients) :
    A.orient.d = A.a := rfl

/-- The second column of a real two-dimensional orthogonal matrix is one of
the two signed quarter turns of its first column. -/
theorem OrthogonalCoefficients.second_column_cases (A : OrthogonalCoefficients) :
    (A.b = -A.c ∧ A.d = A.a) ∨ (A.b = A.c ∧ A.d = -A.a) := by
  have hdet : (A.a * A.d - A.b * A.c) ^ 2 = 1 := by
    calc
      (A.a * A.d - A.b * A.c) ^ 2 =
          (A.a ^ 2 + A.c ^ 2) * (A.b ^ 2 + A.d ^ 2) -
            (A.a * A.b + A.c * A.d) ^ 2 := by ring
      _ = 1 := by rw [A.first_unit, A.second_unit, A.orthogonal]; norm_num
  rcases (sq_eq_one_iff.mp hdet) with hdet | hdet
  · left
    constructor
    · calc
        A.b = (A.a ^ 2 + A.c ^ 2) * A.b := by rw [A.first_unit, one_mul]
        _ = A.a * (A.a * A.b + A.c * A.d) -
            A.c * (A.a * A.d - A.b * A.c) := by ring
        _ = -A.c := by rw [A.orthogonal, hdet]; ring
    · calc
        A.d = (A.a ^ 2 + A.c ^ 2) * A.d := by rw [A.first_unit, one_mul]
        _ = A.c * (A.a * A.b + A.c * A.d) +
            A.a * (A.a * A.d - A.b * A.c) := by ring
        _ = A.a := by rw [A.orthogonal, hdet]; ring
  · right
    constructor
    · calc
        A.b = (A.a ^ 2 + A.c ^ 2) * A.b := by rw [A.first_unit, one_mul]
        _ = A.a * (A.a * A.b + A.c * A.d) -
            A.c * (A.a * A.d - A.b * A.c) := by ring
        _ = A.c := by rw [A.orthogonal, hdet]; ring
    · calc
        A.d = (A.a ^ 2 + A.c ^ 2) * A.d := by rw [A.first_unit, one_mul]
        _ = A.c * (A.a * A.b + A.c * A.d) +
            A.a * (A.a * A.d - A.b * A.c) := by ring
        _ = -A.a := by rw [A.orthogonal, hdet]; ring

def reflectSecond (v : Plane) : Plane := point (v 0) (-v 1)

@[simp] theorem reflectSecond_zero (v : Plane) : reflectSecond v 0 = v 0 := rfl

@[simp] theorem reflectSecond_one (v : Plane) : reflectSecond v 1 = -v 1 := rfl

@[simp] theorem reflectSecond_involutive (v : Plane) :
    reflectSecond (reflectSecond v) = v := by
  ext k
  fin_cases k <;> simp [reflectSecond, point]

theorem reflectSecond_mem_centeredSquare_iff (v : Plane) :
    reflectSecond v ∈ CenteredSquare ↔ v ∈ CenteredSquare := by
  rw [mem_centeredSquare_iff, mem_centeredSquare_iff]
  simp only [reflectSecond_zero, reflectSecond_one]
  constructor
  · rintro ⟨hx₀, hx₁, hy₀, hy₁⟩
    exact ⟨hx₀, hx₁, by linarith, by linarith⟩
  · rintro ⟨hx₀, hx₁, hy₀, hy₁⟩
    exact ⟨hx₀, hx₁, by linarith, by linarith⟩

private theorem toFrame_orient_reflected (A : OrthogonalCoefficients)
    (h : A.b = A.c ∧ A.d = -A.a) (v : Plane) :
    A.toFrame v = A.orient.toFrame (reflectSecond v) := by
  rcases h with ⟨hb, hd⟩
  rw [A.toFrame_apply, A.orient.toFrame_apply]
  ext k
  fin_cases k <;> simp [OrthogonalCoefficients.orient, rotationCoefficients,
    reflectSecond, point, hb, hd]

/-- Changing the determinant sign of a frame representative by an internal
reflection does not change the placed square. -/
theorem placedSquare_orient (c : Plane) (A : OrthogonalCoefficients) :
    placedSquare c A.toFrame = placedSquare c A.orient.toFrame := by
  rcases A.second_column_cases with h | h
  · have hframe : A.toFrame = A.orient.toFrame := by
      ext v k
      rw [A.toFrame_apply, A.orient.toFrame_apply]
      fin_cases k <;>
        simp [OrthogonalCoefficients.orient, rotationCoefficients, point, h.1, h.2]
    rw [hframe]
  · ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨reflectSecond v, (reflectSecond_mem_centeredSquare_iff v).2 hv, ?_⟩
      exact congrArg (fun w => c + w) (toFrame_orient_reflected A h v).symm
    · rintro ⟨v, hv, rfl⟩
      refine ⟨reflectSecond v, (reflectSecond_mem_centeredSquare_iff _).1 ?_, ?_⟩
      · simpa only [reflectSecond_involutive] using hv
      · have hm := toFrame_orient_reflected A h (reflectSecond v)
        simpa only [reflectSecond_involutive] using congrArg (fun w => c + w) hm

theorem vertexInequalities_orient_iff {r : ℝ≥0} (c : Plane)
    (A : OrthogonalCoefficients) :
    VertexInequalities r c A.orient ↔ VertexInequalities r c A := by
  rw [vertex_inequalities_iff_inside, vertex_inequalities_iff_inside,
    ← placedSquare_orient]

theorem fourAxisSeparation_orient_iff (c d : Plane)
    (A B : OrthogonalCoefficients) :
    FourAxisSeparation c d A.orient B.orient ↔ FourAxisSeparation c d A B := by
  rw [← coefficient_disjoint_iff_four_axes, ← coefficient_disjoint_iff_four_axes,
    ← placedSquare_orient c A, ← placedSquare_orient d B]

/-- The exact edge-constraint model after eliminating the two redundant
matrix entries of every frame. -/
structure OrientedEdgeConstraintPacking (n : ℕ) (r : ℝ≥0) where
  centers : Fin n → Plane
  a : Fin n → ℝ
  p : Fin n → ℝ
  unit : ∀ i, a i ^ 2 + p i ^ 2 = 1
  vertices : ∀ i, VertexInequalities r (centers i)
    (rotationCoefficients (a i) (p i) (unit i))
  separations : ∀ i j, i < j → FourAxisSeparation
    (centers i) (centers j)
    (rotationCoefficients (a i) (p i) (unit i))
    (rotationCoefficients (a j) (p j) (unit j))

def OrientedEdgeConstraintPacking.toEdgeConstraints {n : ℕ} {r : ℝ≥0}
    (P : OrientedEdgeConstraintPacking n r) : EdgeConstraintPacking n r where
  centers := P.centers
  coefficients i := rotationCoefficients (P.a i) (P.p i) (P.unit i)
  vertices := P.vertices
  separations := P.separations

def EdgeConstraintPacking.toOriented {n : ℕ} {r : ℝ≥0}
    (P : EdgeConstraintPacking n r) : OrientedEdgeConstraintPacking n r where
  centers := P.centers
  a i := (P.coefficients i).a
  p i := (P.coefficients i).c
  unit i := (P.coefficients i).first_unit
  vertices i := (vertexInequalities_orient_iff _ _).2 (P.vertices i)
  separations i j hij := (fourAxisSeparation_orient_iff _ _ _ _).2
    (P.separations i j hij)

theorem oriented_edge_constraints_packing_iff (n : ℕ) (r : ℝ≥0) :
    Nonempty (OrientedEdgeConstraintPacking n r) ↔
      Nonempty (Packing n UnitSquare (Circle r)) := by
  constructor
  · rintro ⟨P⟩
    exact (edge_constraints_packing_iff n r).mp ⟨P.toEdgeConstraints⟩
  · intro h
    obtain ⟨P⟩ := (edge_constraints_packing_iff n r).mpr h
    exact ⟨P.toOriented⟩

theorem normalized_oriented_edge_constraints_packing_iff
    (n : ℕ) (r : ℝ≥0) (i : Fin n) :
    (∃ P : OrientedEdgeConstraintPacking n r, P.a i = 1 ∧ P.p i = 0) ↔
      Nonempty (Packing n UnitSquare (Circle r)) := by
  constructor
  · rintro ⟨P, ha, hp⟩
    apply (normalized_edge_constraints_packing_iff n r i).mp
    refine ⟨P.toEdgeConstraints, ?_⟩
    ext <;>
      simp [OrientedEdgeConstraintPacking.toEdgeConstraints, rotationCoefficients,
        identityCoefficients, ha, hp]
  · intro h
    obtain ⟨P, hi⟩ := (normalized_edge_constraints_packing_iff n r i).mpr h
    refine ⟨P.toOriented, ?_, ?_⟩
    · simp [EdgeConstraintPacking.toOriented, hi, identityCoefficients]
    · simp [EdgeConstraintPacking.toOriented, hi, identityCoefficients]

end ThreeSquares
