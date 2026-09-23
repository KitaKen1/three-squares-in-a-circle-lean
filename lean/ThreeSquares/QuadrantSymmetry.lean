import ThreeSquares.RationalQuadrantCover

/-! # Reducing the twenty-four quadrant boxes to two representatives

The eight symmetries of the axis-parallel square act on the whole oriented
packing model.  They fix the circle and the centered square, commute with
rotation frames up to reversing the sine for reflections, and therefore keep
the first square normalized.  Together with exchanging the two remaining
labels, they move every smaller FC packing into one of the two
representative closed quadrant boxes.  Boundary coordinates are handled by
closed half-intervals, so a center on an axis is never lost.
-/

open scoped NNReal
open SquarePacking Set

noncomputable section

namespace ThreeSquares

/-- The eight signed coordinate permutations, in the same order as
`RationalPackingFormula.quadrantSymmetry`. -/
def planeSymmetry : Fin 8 → Plane → Plane := ![
  fun v => point (v 0) (v 1),
  fun v => point (-v 0) (v 1),
  fun v => point (v 0) (-v 1),
  fun v => point (-v 0) (-v 1),
  fun v => point (v 1) (v 0),
  fun v => point (-v 1) (v 0),
  fun v => point (v 1) (-v 0),
  fun v => point (-v 1) (-v 0)]

/-- Inverse symmetry index: only the two quarter turns are exchanged. -/
def planeSymmetryInv : Fin 8 → Fin 8 := ![0, 1, 2, 3, 4, 6, 5, 7]

/-- Determinant of each signed coordinate permutation. -/
def symmetrySign : Fin 8 → ℝ := ![1, -1, -1, 1, -1, 1, 1, -1]

theorem symmetrySign_sq (g : Fin 8) : symmetrySign g ^ 2 = 1 := by
  fin_cases g <;> norm_num [symmetrySign]

theorem symmetric_unit (g : Fin 8) {a p : ℝ} (hunit : a ^ 2 + p ^ 2 = 1) :
    a ^ 2 + (symmetrySign g * p) ^ 2 = 1 := by
  rw [mul_pow, symmetrySign_sq, one_mul, hunit]

@[simp] theorem planeSymmetry_inv (g : Fin 8) (v : Plane) :
    planeSymmetry g (planeSymmetry (planeSymmetryInv g) v) = v := by
  ext k
  fin_cases g <;> fin_cases k <;> simp [planeSymmetry, planeSymmetryInv, point]

theorem planeSymmetry_add (g : Fin 8) (u w : Plane) :
    planeSymmetry g (u + w) = planeSymmetry g u + planeSymmetry g w := by
  ext k
  fin_cases g <;> fin_cases k <;> simp [planeSymmetry, point] <;> ring

theorem planeSymmetry_injective (g : Fin 8) : Function.Injective (planeSymmetry g) := by
  intro u w h
  ext k
  have h0 := congrArg (fun z : Plane => z 0) h
  have h1 := congrArg (fun z : Plane => z 1) h
  fin_cases g <;> fin_cases k <;>
    simp [planeSymmetry, point] at h0 h1 ⊢ <;> linarith

theorem planeSymmetry_norm_sq (g : Fin 8) (v : Plane) :
    planeSymmetry g v 0 ^ 2 + planeSymmetry g v 1 ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  fin_cases g <;> simp [planeSymmetry, point] <;> ring

theorem planeSymmetry_mem_circle_iff (g : Fin 8) (r : ℝ≥0) (v : Plane) :
    planeSymmetry g v ∈ Circle r ↔ v ∈ Circle r := by
  change planeSymmetry g v 0 ^ 2 + planeSymmetry g v 1 ^ 2 < (r : ℝ) ^ 2 ↔
    v 0 ^ 2 + v 1 ^ 2 < (r : ℝ) ^ 2
  rw [planeSymmetry_norm_sq]

theorem planeSymmetry_mem_centeredSquare_iff (g : Fin 8) (v : Plane) :
    planeSymmetry g v ∈ CenteredSquare ↔ v ∈ CenteredSquare := by
  rw [mem_centeredSquare_iff, mem_centeredSquare_iff]
  constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
    fin_cases g <;> simp [planeSymmetry, point] at h₁ h₂ h₃ h₄ ⊢ <;> linarith

/-- A global symmetry commutes with a rotation frame, reversing the rotation
for the four reflections. -/
theorem planeSymmetry_rotation (g : Fin 8) {a p : ℝ} (hunit : a ^ 2 + p ^ 2 = 1)
    (h' : a ^ 2 + (symmetrySign g * p) ^ 2 = 1) (v : Plane) :
    planeSymmetry g ((rotationCoefficients a p hunit).toFrame v) =
      (rotationCoefficients a (symmetrySign g * p) h').toFrame (planeSymmetry g v) := by
  ext k
  fin_cases g <;> fin_cases k <;>
    simp [planeSymmetry, symmetrySign, rotationCoefficients, point] <;> ring

/-- The image of a placed square under a global symmetry is the placed square
at the moved center with the transformed rotation. -/
theorem placedSquare_symmetry (g : Fin 8) (c : Plane) {a p : ℝ}
    (hunit : a ^ 2 + p ^ 2 = 1) (h' : a ^ 2 + (symmetrySign g * p) ^ 2 = 1) :
    placedSquare (planeSymmetry g c) (rotationCoefficients a (symmetrySign g * p) h').toFrame =
      planeSymmetry g '' placedSquare c (rotationCoefficients a p hunit).toFrame := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    let v := planeSymmetry (planeSymmetryInv g) w
    have hv : v ∈ CenteredSquare := by
      rw [← planeSymmetry_mem_centeredSquare_iff g]
      simpa [v] using hw
    refine ⟨c + (rotationCoefficients a p hunit).toFrame v, ⟨v, hv, rfl⟩, ?_⟩
    rw [planeSymmetry_add, planeSymmetry_rotation g hunit h']
    simp [v]
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨planeSymmetry g v, (planeSymmetry_mem_centeredSquare_iff g v).2 hv, ?_⟩
    rw [planeSymmetry_add, planeSymmetry_rotation g hunit h']

theorem vertexInequalities_symmetry_iff (g : Fin 8) {r : ℝ≥0} (c : Plane) {a p : ℝ}
    (hunit : a ^ 2 + p ^ 2 = 1) (h' : a ^ 2 + (symmetrySign g * p) ^ 2 = 1) :
    VertexInequalities r (planeSymmetry g c)
        (rotationCoefficients a (symmetrySign g * p) h') ↔
      VertexInequalities r c (rotationCoefficients a p hunit) := by
  rw [vertex_inequalities_iff_inside, vertex_inequalities_iff_inside,
    placedSquare_symmetry g c hunit h', Set.image_subset_iff]
  constructor
  · intro h z hz
    exact (planeSymmetry_mem_circle_iff g r z).1 (h hz)
  · intro h z hz
    exact (planeSymmetry_mem_circle_iff g r z).2 (h hz)

theorem fourAxisSeparation_symmetry_iff (g : Fin 8) (c d : Plane) {a p b q : ℝ}
    (haunit : a ^ 2 + p ^ 2 = 1) (hbunit : b ^ 2 + q ^ 2 = 1)
    (ha' : a ^ 2 + (symmetrySign g * p) ^ 2 = 1)
    (hb' : b ^ 2 + (symmetrySign g * q) ^ 2 = 1) :
    FourAxisSeparation (planeSymmetry g c) (planeSymmetry g d)
        (rotationCoefficients a (symmetrySign g * p) ha')
        (rotationCoefficients b (symmetrySign g * q) hb') ↔
      FourAxisSeparation c d (rotationCoefficients a p haunit)
        (rotationCoefficients b q hbunit) := by
  rw [← coefficient_disjoint_iff_four_axes, ← coefficient_disjoint_iff_four_axes,
    placedSquare_symmetry g c haunit ha', placedSquare_symmetry g d hbunit hb',
    Set.disjoint_image_iff (planeSymmetry_injective g)]

theorem OrientedEdgeConstraintPacking.disjoint_of_ne {n : ℕ} {r : ℝ≥0}
    (P : OrientedEdgeConstraintPacking n r) {i j : Fin n} (hij : i ≠ j) :
    Disjoint
      (placedSquare (P.centers i) (rotationCoefficients (P.a i) (P.p i) (P.unit i)).toFrame)
      (placedSquare (P.centers j) (rotationCoefficients (P.a j) (P.p j) (P.unit j)).toFrame) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact (coefficient_disjoint_iff_four_axes _ _ _ _).2 (P.separations i j h)
  · exact ((coefficient_disjoint_iff_four_axes _ _ _ _).2 (P.separations j i h)).symm

/-- Apply a global square symmetry and an injective relabeling to an exact
oriented packing model. -/
def OrientedEdgeConstraintPacking.transform {n : ℕ} {r : ℝ≥0}
    (P : OrientedEdgeConstraintPacking n r) (g : Fin 8) (σ : Fin n → Fin n)
    (hσ : Function.Injective σ) : OrientedEdgeConstraintPacking n r where
  centers i := planeSymmetry g (P.centers (σ i))
  a i := P.a (σ i)
  p i := symmetrySign g * P.p (σ i)
  unit i := symmetric_unit g (P.unit (σ i))
  vertices i := (vertexInequalities_symmetry_iff g _ (P.unit (σ i)) _).2 (P.vertices (σ i))
  separations i j hij := by
    apply (fourAxisSeparation_symmetry_iff g _ _ (P.unit (σ i)) (P.unit (σ j)) _ _).2
    apply (coefficient_disjoint_iff_four_axes _ _ _ _).1
    exact P.disjoint_of_ne (hσ.ne (ne_of_lt hij))

namespace RationalPackingFormula

private theorem mem_halfInterval_side {x : ℝ} (hx : |x| < 11 / 16) :
    (halfInterval (nonnegativeSide x)).Contains x := by
  obtain ⟨hxl, hxu⟩ := abs_lt.mp hx
  by_cases hx0 : 0 ≤ x
  · simpa [halfInterval, nonnegativeSide, hx0, RationalInterval.Contains] using
      (show 0 ≤ x ∧ x ≤ 11 / 16 from ⟨hx0, le_of_lt hxu⟩)
  · have hxneg : x < 0 := lt_of_not_ge hx0
    simpa [halfInterval, nonnegativeSide, hx0, RationalInterval.Contains, neg_div] using
      (show -(11 / 16) ≤ x ∧ x ≤ 0 from ⟨le_of_lt hxl, le_of_lt hxneg⟩)

/-- Reflecting a coordinate moves it to the opposite closed half-interval;
a zero coordinate lies in both. -/
private theorem mem_halfInterval_not_side {x : ℝ} (hx : |x| < 11 / 16) :
    (halfInterval (!nonnegativeSide x)).Contains (-x) := by
  obtain ⟨hxl, hxu⟩ := abs_lt.mp hx
  by_cases hx0 : 0 ≤ x
  · simp only [nonnegativeSide, hx0, decide_true, Bool.not_true, halfInterval,
      RationalInterval.Contains]
    constructor <;> push_cast <;> linarith
  · have hxneg : x < 0 := lt_of_not_ge hx0
    simp only [nonnegativeSide, hx0, decide_false, Bool.not_false, halfInterval,
      RationalInterval.Contains]
    constructor <;> push_cast <;> linarith

theorem planeSymmetry_mem_quadrant_halves (g : Fin 8) {c : Plane}
    (h0 : |c 0| < 11 / 16) (h1 : |c 1| < 11 / 16) :
    (halfInterval (quadrantSymmetry g (quadrantOf c)).1).Contains (planeSymmetry g c 0) ∧
      (halfInterval (quadrantSymmetry g (quadrantOf c)).2).Contains (planeSymmetry g c 1) := by
  fin_cases g <;> simp only [quadrantSymmetry, planeSymmetry, quadrantOf] <;>
    (try simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, point_zero,
      point_one, Matrix.cons_val_zero, Matrix.cons_val_one]) <;>
    first
    | exact ⟨mem_halfInterval_side h0, mem_halfInterval_side h1⟩
    | exact ⟨mem_halfInterval_not_side h0, mem_halfInterval_side h1⟩
    | exact ⟨mem_halfInterval_side h0, mem_halfInterval_not_side h1⟩
    | exact ⟨mem_halfInterval_not_side h0, mem_halfInterval_not_side h1⟩
    | exact ⟨mem_halfInterval_side h1, mem_halfInterval_side h0⟩
    | exact ⟨mem_halfInterval_not_side h1, mem_halfInterval_side h0⟩
    | exact ⟨mem_halfInterval_side h1, mem_halfInterval_not_side h0⟩
    | exact ⟨mem_halfInterval_not_side h1, mem_halfInterval_not_side h0⟩

theorem remainingSquareRelabel_zero (swap : Bool) : remainingSquareRelabel swap 0 = 0 := by
  cases swap <;> rfl

theorem remainingSquareRelabel_injective (swap : Bool) :
    Function.Injective (remainingSquareRelabel swap) := by
  cases swap <;> decide

/-- The subcritical eight-variable model obtained from a normalized oriented
packing, as in the existing radius-elimination bridge. -/
def orientedSubcritical {r : ℝ≥0} (P : OrientedEdgeConstraintPacking 3 r)
    (hr : r < radius) : SubcriticalRationalRotationPacking 3 :=
  P.toQuadrant.toRational.toSubcritical hr

theorem orientedSubcritical_t_zero {r : ℝ≥0} (P : OrientedEdgeConstraintPacking 3 r)
    (hr : r < radius) (ha : P.a 0 = 1) (hp : P.p 0 = 0) :
    (orientedSubcritical P hr).t 0 = 0 := by
  change quadrantP (P.a 0) (P.p 0) / (1 + quadrantA (P.a 0) (P.p 0)) = 0
  simp [quadrantA, quadrantP, ha, hp]

/-- If a symmetry and relabeling move the quadrant pattern of a normalized
packing to `representative`, the transformed packing gives a solution of the
eight-variable formula in the representative closed box. -/
theorem transformed_packing_in_representative_box {r : ℝ≥0}
    (P : OrientedEdgeConstraintPacking 3 r) (hr : r < radius)
    (ha : P.a 0 = 1) (hp : P.p 0 = 0) (g : Fin 8) (swap : Bool)
    (representative : Fin 3 → Quadrant)
    (hg : ∀ i, quadrantSymmetry g
      (chosenQuadrants (orientedSubcritical P hr) (remainingSquareRelabel swap i)) =
        representative i) :
    ∃ x : Fin 8 → ℝ, (quadrantBox representative).Contains x ∧ formula.Holds x := by
  let σ := remainingSquareRelabel swap
  let P' := P.transform g σ (remainingSquareRelabel_injective swap)
  let Q := orientedSubcritical P' hr
  have hσ0 : σ 0 = 0 := remainingSquareRelabel_zero swap
  have ha' : P'.a 0 = 1 := by
    change P.a (σ 0) = 1
    rw [hσ0, ha]
  have hp' : P'.p 0 = 0 := by
    change symmetrySign g * P.p (σ 0) = 0
    rw [hσ0, hp, mul_zero]
  have hbound (j : Fin 3) (k : Fin 2) : |P.centers j k| < 11 / 16 :=
    strict_candidate_center_coordinate_abs_lt ((orientedSubcritical P hr).vertices j) k
  have hc (i : Fin 3) :
      (halfInterval (representative i).1).Contains (Q.centers i 0) ∧
        (halfInterval (representative i).2).Contains (Q.centers i 1) := by
    rw [← hg i]
    exact planeSymmetry_mem_quadrant_halves g (hbound (σ i) 0) (hbound (σ i) 1)
  refine ⟨assignment Q, ?_, formula_holds Q (orientedSubcritical_t_zero P' hr ha' hp')⟩
  intro k
  fin_cases k
  · exact (hc 0).1
  · exact (hc 0).2
  · exact (hc 1).1
  · exact (hc 1).2
  · exact (hc 2).1
  · exact (hc 2).2
  · simpa [quadrantBox, assignment, RationalInterval.Contains] using
      And.intro (Q.t_nonneg 1) (Q.t_le_one 1)
  · simpa [quadrantBox, assignment, RationalInterval.Contains] using
      And.intro (Q.t_nonneg 2) (Q.t_le_one 2)

/-- Every FC packing below the candidate radius has an eight-variable witness
in one of the two representative closed quadrant boxes. -/
theorem smaller_fc_packing_in_representative_box {r : ℝ≥0}
    (hr : r < radius) (h : Nonempty (Packing 3 UnitSquare (Circle r))) :
    ∃ x : Fin 8 → ℝ,
      ((quadrantBox adjacentRepresentative).Contains x ∨
        (quadrantBox oppositeRepresentative).Contains x) ∧ formula.Holds x := by
  obtain ⟨P, ha, hp⟩ := (normalized_oriented_edge_constraints_packing_iff 3 r 0).mpr h
  let q : QuadrantAssignment :=
    ⟨chosenQuadrants (orientedSubcritical P hr),
      chosenQuadrants_injective (orientedSubcritical P hr)⟩
  rcases quadrant_assignment_two_orbits q with ⟨g, swap, hg⟩ | ⟨g, swap, hg⟩
  · obtain ⟨x, hx, hf⟩ :=
      transformed_packing_in_representative_box P hr ha hp g swap _ hg
    exact ⟨x, Or.inl hx, hf⟩
  · obtain ⟨x, hx, hf⟩ :=
      transformed_packing_in_representative_box P hr ha hp g swap _ hg
    exact ⟨x, Or.inr hx, hf⟩

/-- Checked certificates for the two representative boxes localize every
smaller FC packing, up to symmetry, in one of their residual leaves. -/
theorem representative_certificates_localize_smaller_fc_packing
    (adjacent opposite : IntervalCertificate 8)
    (hadjacent : adjacent.check formula (quadrantBox adjacentRepresentative) = true)
    (hopposite : opposite.check formula (quadrantBox oppositeRepresentative) = true)
    {r : ℝ≥0} (hr : r < radius) (h : Nonempty (Packing 3 UnitSquare (Circle r))) :
    ∃ x : Fin 8 → ℝ, formula.Holds x ∧
      ((∃ C ∈ adjacent.residuals (quadrantBox adjacentRepresentative), C.Contains x) ∨
        (∃ C ∈ opposite.residuals (quadrantBox oppositeRepresentative), C.Contains x)) := by
  obtain ⟨x, hx | hx, hf⟩ := smaller_fc_packing_in_representative_box hr h
  · exact ⟨x, hf, Or.inl (adjacent.check_sound formula hadjacent hx hf)⟩
  · exact ⟨x, hf, Or.inr (opposite.check_sound formula hopposite hx hf)⟩

/-- Two empty checked certificates, one for each symmetry representative,
prove the unrestricted lower bound. -/
theorem global_lower_bound_of_two_representative_certificates
    (adjacent opposite : IntervalCertificate 8)
    (hadjacent : adjacent.check formula (quadrantBox adjacentRepresentative) = true)
    (hopposite : opposite.check formula (quadrantBox oppositeRepresentative) = true)
    (hadjacentEmpty : adjacent.residuals (quadrantBox adjacentRepresentative) = [])
    (hoppositeEmpty : opposite.residuals (quadrantBox oppositeRepresentative) = []) :
    GlobalLowerBound := by
  intro r hr
  by_contra hn
  obtain ⟨x, hx | hx, hf⟩ :=
    smaller_fc_packing_in_representative_box (lt_of_not_ge hn) hr
  · exact adjacent.exclude_sound formula hadjacent hadjacentEmpty ⟨x, hx, hf⟩
  · exact opposite.exclude_sound formula hopposite hoppositeEmpty ⟨x, hx, hf⟩

end RationalPackingFormula

end ThreeSquares
