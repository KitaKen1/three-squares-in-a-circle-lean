import ThreeSquares.OrientedPacking

/-! # Rational rotation parameters for square packings

Quarter-turn symmetries of the centered square move every unit vector to the
closed first quadrant without changing the placed square.  The first-quadrant
unit circle is then represented exactly by `t = p / (1 + a)` in `[0,1]`.
-/

open scoped NNReal
open SquarePacking Set

noncomputable section

namespace ThreeSquares

def rotateQuarter (v : Plane) : Plane := point (-v 1) (v 0)

def rotateQuarterInv (v : Plane) : Plane := point (v 1) (-v 0)

@[simp] theorem rotateQuarter_inv (v : Plane) :
    rotateQuarter (rotateQuarterInv v) = v := by
  ext k
  fin_cases k <;> simp [rotateQuarter, rotateQuarterInv, point]

@[simp] theorem rotateQuarterInv_quarter (v : Plane) :
    rotateQuarterInv (rotateQuarter v) = v := by
  ext k
  fin_cases k <;> simp [rotateQuarter, rotateQuarterInv, point]

theorem rotateQuarter_mem_centeredSquare_iff (v : Plane) :
    rotateQuarter v ∈ CenteredSquare ↔ v ∈ CenteredSquare := by
  rw [mem_centeredSquare_iff, mem_centeredSquare_iff]
  simp only [rotateQuarter, point_zero, point_one]
  constructor <;> rintro ⟨hx₀, hx₁, hy₀, hy₁⟩ <;>
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem rotateQuarterInv_mem_centeredSquare_iff (v : Plane) :
    rotateQuarterInv v ∈ CenteredSquare ↔ v ∈ CenteredSquare := by
  rw [mem_centeredSquare_iff, mem_centeredSquare_iff]
  simp only [rotateQuarterInv, point_zero, point_one]
  constructor <;> rintro ⟨hx₀, hx₁, hy₀, hy₁⟩ <;>
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem rotationCoefficients_quarter_apply {a p : ℝ}
    (hunit : a ^ 2 + p ^ 2 = 1)
    (hquarter : (-p) ^ 2 + a ^ 2 = 1) (v : Plane) :
    (rotationCoefficients (-p) a hquarter).toFrame v =
      (rotationCoefficients a p hunit).toFrame (rotateQuarter v) := by
  rw [OrthogonalCoefficients.toFrame_apply, OrthogonalCoefficients.toFrame_apply]
  ext k
  fin_cases k <;> simp [rotationCoefficients, rotateQuarter, point] <;> ring

/-- Composing a frame with an internal quarter turn leaves the placed square
unchanged. -/
theorem placedSquare_rotation_quarter (c : Plane) {a p : ℝ}
    (hunit : a ^ 2 + p ^ 2 = 1) :
    placedSquare c (rotationCoefficients a p hunit).toFrame =
      placedSquare c
        (rotationCoefficients (-p) a (by nlinarith [hunit])).toFrame := by
  let hquarter : (-p) ^ 2 + a ^ 2 = 1 := by nlinarith [hunit]
  change placedSquare c (rotationCoefficients a p hunit).toFrame =
    placedSquare c (rotationCoefficients (-p) a hquarter).toFrame
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨rotateQuarterInv v, (rotateQuarterInv_mem_centeredSquare_iff v).2 hv, ?_⟩
    have hm := rotationCoefficients_quarter_apply hunit hquarter (rotateQuarterInv v)
    simpa only [rotateQuarter_inv] using congrArg (fun w => c + w) hm
  · rintro ⟨v, hv, rfl⟩
    refine ⟨rotateQuarter v, (rotateQuarter_mem_centeredSquare_iff v).2 hv, ?_⟩
    exact congrArg (fun w => c + w)
      (rotationCoefficients_quarter_apply hunit hquarter v).symm

def quadrantA (a p : ℝ) : ℝ :=
  if 0 ≤ a then if 0 ≤ p then a else -p else if 0 ≤ p then p else -a

def quadrantP (a p : ℝ) : ℝ :=
  if 0 ≤ a then if 0 ≤ p then p else a else if 0 ≤ p then -a else -p

theorem quadrant_nonneg (a p : ℝ) :
    0 ≤ quadrantA a p ∧ 0 ≤ quadrantP a p := by
  by_cases ha : 0 ≤ a <;> by_cases hp : 0 ≤ p
  · simp only [quadrantA, quadrantP, if_pos ha, if_pos hp]
    exact ⟨ha, hp⟩
  · simp only [quadrantA, quadrantP, if_pos ha, if_neg hp]
    exact ⟨by linarith, ha⟩
  · simp only [quadrantA, quadrantP, if_neg ha, if_pos hp]
    exact ⟨hp, by linarith⟩
  · simp only [quadrantA, quadrantP, if_neg ha, if_neg hp]
    exact ⟨by linarith, by linarith⟩

theorem quadrant_unit {a p : ℝ} (hunit : a ^ 2 + p ^ 2 = 1) :
    quadrantA a p ^ 2 + quadrantP a p ^ 2 = 1 := by
  by_cases ha : 0 ≤ a <;> by_cases hp : 0 ≤ p <;>
    simp [quadrantA, quadrantP, ha, hp] <;> nlinarith [hunit]

/-- A square frame can be moved to the closed first quadrant using only its
internal quarter-turn symmetry. -/
theorem placedSquare_quadrant (c : Plane) {a p : ℝ}
    (hunit : a ^ 2 + p ^ 2 = 1) :
    placedSquare c (rotationCoefficients a p hunit).toFrame =
      placedSquare c
        (rotationCoefficients (quadrantA a p) (quadrantP a p)
          (quadrant_unit hunit)).toFrame := by
  by_cases ha : 0 ≤ a <;> by_cases hp : 0 ≤ p
  · simp [quadrantA, quadrantP, ha, hp]
  · simpa [quadrantA, quadrantP, ha, hp] using placedSquare_rotation_quarter c hunit
  · have h₁ : (-p) ^ 2 + a ^ 2 = 1 := by nlinarith [hunit]
    have h₂ : (-a) ^ 2 + (-p) ^ 2 = 1 := by nlinarith [hunit]
    have h₃ : p ^ 2 + (-a) ^ 2 = 1 := by nlinarith [hunit]
    calc
      placedSquare c (rotationCoefficients a p hunit).toFrame =
          placedSquare c (rotationCoefficients (-p) a h₁).toFrame := by
            simpa using placedSquare_rotation_quarter c hunit
      _ = placedSquare c (rotationCoefficients (-a) (-p) h₂).toFrame := by
            simpa using placedSquare_rotation_quarter c h₁
      _ = placedSquare c (rotationCoefficients p (-a) h₃).toFrame := by
            simpa using placedSquare_rotation_quarter c h₂
      _ = _ := by simp [quadrantA, quadrantP, ha, hp]
  · have h₁ : (-p) ^ 2 + a ^ 2 = 1 := by nlinarith [hunit]
    have h₂ : (-a) ^ 2 + (-p) ^ 2 = 1 := by nlinarith [hunit]
    calc
      placedSquare c (rotationCoefficients a p hunit).toFrame =
          placedSquare c (rotationCoefficients (-p) a h₁).toFrame := by
            simpa using placedSquare_rotation_quarter c hunit
      _ = placedSquare c (rotationCoefficients (-a) (-p) h₂).toFrame := by
            simpa using placedSquare_rotation_quarter c h₁
      _ = _ := by simp [quadrantA, quadrantP, ha, hp]

theorem vertexInequalities_quadrant_iff {r : ℝ≥0} (c : Plane) {a p : ℝ}
    (hunit : a ^ 2 + p ^ 2 = 1) :
    VertexInequalities r c
        (rotationCoefficients (quadrantA a p) (quadrantP a p) (quadrant_unit hunit)) ↔
      VertexInequalities r c (rotationCoefficients a p hunit) := by
  rw [vertex_inequalities_iff_inside, vertex_inequalities_iff_inside,
    ← placedSquare_quadrant]

theorem fourAxisSeparation_quadrant_iff (c d : Plane)
    {a p b q : ℝ} (haunit : a ^ 2 + p ^ 2 = 1)
    (hbunit : b ^ 2 + q ^ 2 = 1) :
    FourAxisSeparation c d
        (rotationCoefficients (quadrantA a p) (quadrantP a p) (quadrant_unit haunit))
        (rotationCoefficients (quadrantA b q) (quadrantP b q) (quadrant_unit hbunit)) ↔
      FourAxisSeparation c d (rotationCoefficients a p haunit)
        (rotationCoefficients b q hbunit) := by
  rw [← coefficient_disjoint_iff_four_axes, ← coefficient_disjoint_iff_four_axes,
    ← placedSquare_quadrant c haunit, ← placedSquare_quadrant d hbunit]

structure QuadrantEdgeConstraintPacking (n : ℕ) (r : ℝ≥0) where
  centers : Fin n → Plane
  a : Fin n → ℝ
  p : Fin n → ℝ
  unit : ∀ i, a i ^ 2 + p i ^ 2 = 1
  a_nonneg : ∀ i, 0 ≤ a i
  p_nonneg : ∀ i, 0 ≤ p i
  vertices : ∀ i, VertexInequalities r (centers i)
    (rotationCoefficients (a i) (p i) (unit i))
  separations : ∀ i j, i < j → FourAxisSeparation
    (centers i) (centers j)
    (rotationCoefficients (a i) (p i) (unit i))
    (rotationCoefficients (a j) (p j) (unit j))

def QuadrantEdgeConstraintPacking.toOriented {n : ℕ} {r : ℝ≥0}
    (P : QuadrantEdgeConstraintPacking n r) : OrientedEdgeConstraintPacking n r where
  centers := P.centers
  a := P.a
  p := P.p
  unit := P.unit
  vertices := P.vertices
  separations := P.separations

def OrientedEdgeConstraintPacking.toQuadrant {n : ℕ} {r : ℝ≥0}
    (P : OrientedEdgeConstraintPacking n r) : QuadrantEdgeConstraintPacking n r where
  centers := P.centers
  a i := quadrantA (P.a i) (P.p i)
  p i := quadrantP (P.a i) (P.p i)
  unit i := quadrant_unit (P.unit i)
  a_nonneg i := (quadrant_nonneg (P.a i) (P.p i)).1
  p_nonneg i := (quadrant_nonneg (P.a i) (P.p i)).2
  vertices i := (vertexInequalities_quadrant_iff _ (P.unit i)).2 (P.vertices i)
  separations i j hij :=
    (fourAxisSeparation_quadrant_iff _ _ (P.unit i) (P.unit j)).2
      (P.separations i j hij)

theorem quadrant_edge_constraints_packing_iff (n : ℕ) (r : ℝ≥0) :
    Nonempty (QuadrantEdgeConstraintPacking n r) ↔
      Nonempty (Packing n UnitSquare (Circle r)) := by
  constructor
  · rintro ⟨P⟩
    exact (oriented_edge_constraints_packing_iff n r).mp ⟨P.toOriented⟩
  · intro h
    obtain ⟨P⟩ := (oriented_edge_constraints_packing_iff n r).mpr h
    exact ⟨P.toQuadrant⟩

def rationalCos (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)

def rationalSin (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)

theorem rational_denominator_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

theorem rational_rotation_unit (t : ℝ) :
    rationalCos t ^ 2 + rationalSin t ^ 2 = 1 := by
  have hn : 1 + t ^ 2 ≠ 0 := ne_of_gt (rational_denominator_pos t)
  rw [rationalCos, rationalSin]
  field_simp [hn]
  ring

theorem rationalCos_nonneg {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    0 ≤ rationalCos t := by
  rw [rationalCos]
  exact div_nonneg (by nlinarith) (le_of_lt (rational_denominator_pos t))

theorem rationalSin_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ rationalSin t := by
  rw [rationalSin]
  exact div_nonneg (mul_nonneg (by norm_num) ht) (le_of_lt (rational_denominator_pos t))

/-- Inverse stereographic coordinates on the first-quadrant unit circle. -/
theorem first_quadrant_rational_parameters {a p : ℝ}
    (hunit : a ^ 2 + p ^ 2 = 1) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    let t := p / (1 + a)
    0 ≤ t ∧ t ≤ 1 ∧ a = rationalCos t ∧ p = rationalSin t := by
  let t := p / (1 + a)
  have hden : 0 < 1 + a := by linarith
  have ht₀ : 0 ≤ t := div_nonneg hp (le_of_lt hden)
  have hp₁ : p ≤ 1 := by nlinarith [sq_nonneg a, sq_nonneg (p - 1)]
  have ht₁ : t ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  have ha' : a = rationalCos t := by
    rw [rationalCos]
    dsimp [t]
    field_simp [ne_of_gt hden]
    nlinarith [hunit]
  have hp' : p = rationalSin t := by
    rw [rationalSin]
    dsimp [t]
    field_simp [ne_of_gt hden]
    nlinarith [hunit]
  exact ⟨ht₀, ht₁, ha', hp'⟩

/-- Exact eight-parameter model after normalizing the first square: six center
coordinates and one rational rotation parameter for each remaining square. -/
structure RationalRotationPacking (n : ℕ) (r : ℝ≥0) where
  centers : Fin n → Plane
  t : Fin n → ℝ
  t_nonneg : ∀ i, 0 ≤ t i
  t_le_one : ∀ i, t i ≤ 1
  vertices : ∀ i, VertexInequalities r (centers i)
    (rotationCoefficients (rationalCos (t i)) (rationalSin (t i))
      (rational_rotation_unit (t i)))
  separations : ∀ i j, i < j → FourAxisSeparation
    (centers i) (centers j)
    (rotationCoefficients (rationalCos (t i)) (rationalSin (t i))
      (rational_rotation_unit (t i)))
    (rotationCoefficients (rationalCos (t j)) (rationalSin (t j))
      (rational_rotation_unit (t j)))

def RationalRotationPacking.toQuadrant {n : ℕ} {r : ℝ≥0}
    (P : RationalRotationPacking n r) : QuadrantEdgeConstraintPacking n r where
  centers := P.centers
  a i := rationalCos (P.t i)
  p i := rationalSin (P.t i)
  unit i := rational_rotation_unit (P.t i)
  a_nonneg i := rationalCos_nonneg (P.t_nonneg i) (P.t_le_one i)
  p_nonneg i := rationalSin_nonneg (P.t_nonneg i)
  vertices := P.vertices
  separations := P.separations

def QuadrantEdgeConstraintPacking.toRational {n : ℕ} {r : ℝ≥0}
    (P : QuadrantEdgeConstraintPacking n r) : RationalRotationPacking n r where
  centers := P.centers
  t i := P.p i / (1 + P.a i)
  t_nonneg i := (first_quadrant_rational_parameters (P.unit i)
    (P.a_nonneg i) (P.p_nonneg i)).1
  t_le_one i := (first_quadrant_rational_parameters (P.unit i)
    (P.a_nonneg i) (P.p_nonneg i)).2.1
  vertices i := by
    obtain ⟨_, _, ha, hp⟩ := first_quadrant_rational_parameters
      (P.unit i) (P.a_nonneg i) (P.p_nonneg i)
    have hA :
        rotationCoefficients
            (rationalCos (P.p i / (1 + P.a i)))
            (rationalSin (P.p i / (1 + P.a i)))
            (rational_rotation_unit (P.p i / (1 + P.a i))) =
          rotationCoefficients (P.a i) (P.p i) (P.unit i) := by
      apply OrthogonalCoefficients.ext
      · exact ha.symm
      · exact congrArg Neg.neg hp.symm
      · exact hp.symm
      · exact ha.symm
    rw [hA]
    exact P.vertices i
  separations i j hij := by
    obtain ⟨_, _, hai, hpi⟩ := first_quadrant_rational_parameters
      (P.unit i) (P.a_nonneg i) (P.p_nonneg i)
    obtain ⟨_, _, haj, hpj⟩ := first_quadrant_rational_parameters
      (P.unit j) (P.a_nonneg j) (P.p_nonneg j)
    have hAi :
        rotationCoefficients
            (rationalCos (P.p i / (1 + P.a i)))
            (rationalSin (P.p i / (1 + P.a i)))
            (rational_rotation_unit (P.p i / (1 + P.a i))) =
          rotationCoefficients (P.a i) (P.p i) (P.unit i) := by
      apply OrthogonalCoefficients.ext
      · exact hai.symm
      · exact congrArg Neg.neg hpi.symm
      · exact hpi.symm
      · exact hai.symm
    have hAj :
        rotationCoefficients
            (rationalCos (P.p j / (1 + P.a j)))
            (rationalSin (P.p j / (1 + P.a j)))
            (rational_rotation_unit (P.p j / (1 + P.a j))) =
          rotationCoefficients (P.a j) (P.p j) (P.unit j) := by
      apply OrthogonalCoefficients.ext
      · exact haj.symm
      · exact congrArg Neg.neg hpj.symm
      · exact hpj.symm
      · exact haj.symm
    rw [hAi, hAj]
    exact P.separations i j hij

theorem rational_rotation_packing_iff (n : ℕ) (r : ℝ≥0) :
    Nonempty (RationalRotationPacking n r) ↔
      Nonempty (Packing n UnitSquare (Circle r)) := by
  constructor
  · rintro ⟨P⟩
    exact (quadrant_edge_constraints_packing_iff n r).mp ⟨P.toQuadrant⟩
  · intro h
    obtain ⟨P⟩ := (quadrant_edge_constraints_packing_iff n r).mpr h
    exact ⟨P.toRational⟩

theorem normalized_rational_rotation_packing_iff
    (n : ℕ) (r : ℝ≥0) (i : Fin n) :
    (∃ P : RationalRotationPacking n r, P.t i = 0) ↔
      Nonempty (Packing n UnitSquare (Circle r)) := by
  constructor
  · rintro ⟨P, _⟩
    exact (rational_rotation_packing_iff n r).mp ⟨P⟩
  · intro h
    obtain ⟨P, ha, hp⟩ := (normalized_oriented_edge_constraints_packing_iff n r i).mpr h
    let Q := P.toQuadrant.toRational
    refine ⟨Q, ?_⟩
    change quadrantP (P.a i) (P.p i) / (1 + quadrantA (P.a i) (P.p i)) = 0
    simp [quadrantA, quadrantP, ha, hp]

end ThreeSquares
