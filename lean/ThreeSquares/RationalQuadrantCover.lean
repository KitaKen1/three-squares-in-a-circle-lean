import ThreeSquares.RationalPackingFormula

/-! # The twenty-four center-quadrant boxes in eight variables

Every subcritical model has its three centers in three distinct closed
quadrant boxes. The cover includes coordinate-axis boundaries and leaves both
rational rotation parameters on their full closed interval `[0,1]`.
-/

namespace ThreeSquares
namespace RationalPackingFormula

open scoped NNReal
open SquarePacking

noncomputable section

abbrev Quadrant := Bool × Bool

def nonnegativeSide (x : ℝ) : Bool := decide (0 ≤ x)

def quadrantOf (c : Plane) : Quadrant :=
  (nonnegativeSide (c 0), nonnegativeSide (c 1))

def halfInterval : Bool → RationalInterval
  | false => ⟨-11 / 16, 0⟩
  | true => ⟨0, 11 / 16⟩

/-- The six center coordinates are restricted by a quadrant assignment; the
two rotation parameters retain their complete closed range. -/
def quadrantBox (q : Fin 3 → Quadrant) : RationalBox 8 := ![
  halfInterval (q 0).1, halfInterval (q 0).2,
  halfInterval (q 1).1, halfInterval (q 1).2,
  halfInterval (q 2).1, halfInterval (q 2).2,
  ⟨0, 1⟩, ⟨0, 1⟩]

abbrev QuadrantAssignment := {q : Fin 3 → Quadrant // Function.Injective q}

def chosenQuadrants (P : SubcriticalRationalRotationPacking 3) : Fin 3 → Quadrant :=
  fun i => quadrantOf (P.centers i)

private theorem nonnegativeSide_eq_iff {x y : ℝ} :
    nonnegativeSide x = nonnegativeSide y ↔ (0 ≤ x ↔ 0 ≤ y) := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y <;>
    simp [nonnegativeSide, hx, hy]

private theorem same_side_difference_abs_lt {x y : ℝ}
    (hx : |x| < 11 / 16) (hy : |y| < 11 / 16)
    (hs : nonnegativeSide x = nonnegativeSide y) :
    |y - x| < 11 / 16 := by
  have hs' := nonnegativeSide_eq_iff.mp hs
  obtain ⟨hxl, hxu⟩ := abs_lt.mp hx
  obtain ⟨hyl, hyu⟩ := abs_lt.mp hy
  rw [abs_lt]
  by_cases hx0 : 0 ≤ x
  · have hy0 : 0 ≤ y := hs'.mp hx0
    constructor <;> linarith
  · have hxneg : x < 0 := lt_of_not_ge hx0
    have hyneg : y < 0 := by
      apply lt_of_not_ge
      intro hy0
      exact hx0 (hs'.mpr hy0)
    constructor <;> linarith

private theorem mem_halfInterval_chosen {x : ℝ} (hx : |x| < 11 / 16) :
    (halfInterval (nonnegativeSide x)).Contains x := by
  obtain ⟨hxl, hxu⟩ := abs_lt.mp hx
  by_cases hx0 : 0 ≤ x
  · simpa [halfInterval, nonnegativeSide, hx0, RationalInterval.Contains] using
      (show 0 ≤ x ∧ x ≤ 11 / 16 from ⟨hx0, le_of_lt hxu⟩)
  · have hxneg : x < 0 := lt_of_not_ge hx0
    simpa [halfInterval, nonnegativeSide, hx0, RationalInterval.Contains, neg_div] using
      (show -(11 / 16) ≤ x ∧ x ≤ 0 from ⟨le_of_lt hxl, le_of_lt hxneg⟩)

theorem chosenQuadrants_injective (P : SubcriticalRationalRotationPacking 3) :
    Function.Injective (chosenQuadrants P) := by
  intro i j hq
  by_contra hij
  have hxside : nonnegativeSide (P.centers i 0) =
      nonnegativeSide (P.centers j 0) := congrArg Prod.fst hq
  have hyside : nonnegativeSide (P.centers i 1) =
      nonnegativeSide (P.centers j 1) := congrArg Prod.snd hq
  have hix := strict_candidate_center_coordinate_abs_lt (P.vertices i) 0
  have hiy := strict_candidate_center_coordinate_abs_lt (P.vertices i) 1
  have hjx := strict_candidate_center_coordinate_abs_lt (P.vertices j) 0
  have hjy := strict_candidate_center_coordinate_abs_lt (P.vertices j) 1
  have hdx := same_side_difference_abs_lt hix hjx hxside
  have hdy := same_side_difference_abs_lt hiy hjy hyside
  have hdx2 : (P.centers j 0 - P.centers i 0) ^ 2 < (11 / 16 : ℝ) ^ 2 := by
    nlinarith [sq_abs (P.centers j 0 - P.centers i 0),
      abs_nonneg (P.centers j 0 - P.centers i 0)]
  have hdy2 : (P.centers j 1 - P.centers i 1) ^ 2 < (11 / 16 : ℝ) ^ 2 := by
    nlinarith [sq_abs (P.centers j 1 - P.centers i 1),
      abs_nonneg (P.centers j 1 - P.centers i 1)]
  have hsep : 1 ≤ (P.centers j 0 - P.centers i 0) ^ 2 +
      (P.centers j 1 - P.centers i 1) ^ 2 := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact separated_centers_distance_sq (P.separations i j hlt)
    · have h := separated_centers_distance_sq (P.separations j i hgt)
      nlinarith only [h]
  nlinarith only [hsep, hdx2, hdy2]

theorem assignment_in_chosen_quadrant_box
    (P : SubcriticalRationalRotationPacking 3) :
    (quadrantBox (chosenQuadrants P)).Contains (assignment P) := by
  intro i
  fin_cases i
  · simpa [quadrantBox, chosenQuadrants, quadrantOf, assignment] using
      mem_halfInterval_chosen (strict_candidate_center_coordinate_abs_lt (P.vertices 0) 0)
  · simpa [quadrantBox, chosenQuadrants, quadrantOf, assignment] using
      mem_halfInterval_chosen (strict_candidate_center_coordinate_abs_lt (P.vertices 0) 1)
  · simpa [quadrantBox, chosenQuadrants, quadrantOf, assignment] using
      mem_halfInterval_chosen (strict_candidate_center_coordinate_abs_lt (P.vertices 1) 0)
  · simpa [quadrantBox, chosenQuadrants, quadrantOf, assignment] using
      mem_halfInterval_chosen (strict_candidate_center_coordinate_abs_lt (P.vertices 1) 1)
  · simpa [quadrantBox, chosenQuadrants, quadrantOf, assignment] using
      mem_halfInterval_chosen (strict_candidate_center_coordinate_abs_lt (P.vertices 2) 0)
  · simpa [quadrantBox, chosenQuadrants, quadrantOf, assignment] using
      mem_halfInterval_chosen (strict_candidate_center_coordinate_abs_lt (P.vertices 2) 1)
  · simpa [quadrantBox, assignment, RationalInterval.Contains] using
      And.intro (P.t_nonneg 1) (P.t_le_one 1)
  · simpa [quadrantBox, assignment, RationalInterval.Contains] using
      And.intro (P.t_nonneg 2) (P.t_le_one 2)

theorem assignment_in_one_of_quadrant_boxes
    (P : SubcriticalRationalRotationPacking 3) :
    ∃ q : QuadrantAssignment, (quadrantBox q.1).Contains (assignment P) :=
  ⟨⟨chosenQuadrants P, chosenQuadrants_injective P⟩,
    assignment_in_chosen_quadrant_box P⟩

theorem quadrant_assignments_card : Fintype.card QuadrantAssignment = 24 := by
  decide +kernel

/-- The eight symmetries of the square acting on the four closed quadrant
labels. Complements represent axis reflections and swapping the two Boolean
coordinates represents reflection in the diagonal. -/
def quadrantSymmetry : Fin 8 → Quadrant → Quadrant := ![
  fun q => (q.1, q.2),
  fun q => (Bool.not q.1, q.2),
  fun q => (q.1, Bool.not q.2),
  fun q => (Bool.not q.1, Bool.not q.2),
  fun q => (q.2, q.1),
  fun q => (Bool.not q.2, q.1),
  fun q => (q.2, Bool.not q.1),
  fun q => (Bool.not q.2, Bool.not q.1)]

/-- Optionally exchange the two squares whose orientations remain after the
first square has been normalized. -/
def remainingSquareRelabel : Bool → Fin 3 → Fin 3
  | false => ![0, 1, 2]
  | true => ![0, 2, 1]

def adjacentRepresentative : Fin 3 → Quadrant := ![
  (false, false), (true, false), (false, true)]

def oppositeRepresentative : Fin 3 → Quadrant := ![
  (false, false), (true, false), (true, true)]

def QuadrantAssignment.EquivalentTo (q : QuadrantAssignment)
    (representative : Fin 3 → Quadrant) : Prop :=
  ∃ g : Fin 8, ∃ swap : Bool, ∀ i,
    quadrantSymmetry g (q.1 (remainingSquareRelabel swap i)) = representative i

instance (q : QuadrantAssignment) (representative : Fin 3 → Quadrant) :
    Decidable (q.EquivalentTo representative) := by
  unfold QuadrantAssignment.EquivalentTo
  infer_instance

/-- The twenty-four injective quadrant assignments form exactly the two
expected combinatorial orbits under a global square symmetry and exchange of
the two remaining square labels. -/
theorem quadrant_assignment_two_orbits : ∀ q : QuadrantAssignment,
    q.EquivalentTo adjacentRepresentative ∨ q.EquivalentTo oppositeRepresentative := by
  decide +kernel

/-- Every smaller FC packing is represented in one of exactly twenty-four
closed eight-variable quadrant boxes. -/
theorem smaller_fc_packing_in_one_of_24_quadrant_boxes {r : ℝ≥0}
    (hr : r < radius) (h : Nonempty (Packing 3 UnitSquare (Circle r))) :
    ∃ q : QuadrantAssignment, ∃ x : Fin 8 → ℝ,
      (quadrantBox q.1).Contains x ∧ formula.Holds x := by
  obtain ⟨P, hP⟩ := (normalized_rational_rotation_packing_iff 3 r 0).mpr h
  let Q := P.toSubcritical hr
  obtain ⟨q, hq⟩ := assignment_in_one_of_quadrant_boxes Q
  exact ⟨q, assignment Q, hq, formula_holds Q hP⟩

/-- A checked certificate for every quadrant assignment localizes any smaller
FC packing in a residual leaf of the corresponding certificate.  This bridge
does not rely on the optional reduction of the twenty-four assignments to two
symmetry representatives. -/
theorem quadrant_certificate_family_localizes_smaller_fc_packing
    (certificates : QuadrantAssignment → IntervalCertificate 8)
    (hcheck : ∀ q, (certificates q).check formula (quadrantBox q.1) = true)
    {r : ℝ≥0} (hr : r < radius)
    (h : Nonempty (Packing 3 UnitSquare (Circle r))) :
    ∃ q : QuadrantAssignment, ∃ x : Fin 8 → ℝ,
      ∃ C ∈ (certificates q).residuals (quadrantBox q.1),
        C.Contains x ∧ formula.Holds x := by
  obtain ⟨q, x, hx, hp⟩ := smaller_fc_packing_in_one_of_24_quadrant_boxes hr h
  obtain ⟨C, hC, hCx⟩ :=
    (certificates q).check_sound formula (hcheck q) hx hp
  exact ⟨q, x, C, hC, hCx, hp⟩

/-- Empty checked certificates for all twenty-four closed quadrant boxes prove
the unrestricted lower bound.  Symmetry reduction can reduce computation, but
is not an assumption of this theorem. -/
theorem global_lower_bound_of_empty_quadrant_certificate_family
    (certificates : QuadrantAssignment → IntervalCertificate 8)
    (hcheck : ∀ q, (certificates q).check formula (quadrantBox q.1) = true)
    (hempty : ∀ q, (certificates q).residuals (quadrantBox q.1) = []) :
    GlobalLowerBound := by
  intro r hr
  by_contra hn
  obtain ⟨q, x, hx, hp⟩ :=
    smaller_fc_packing_in_one_of_24_quadrant_boxes (lt_of_not_ge hn) hr
  exact (certificates q).exclude_sound formula (hcheck q) (hempty q)
    ⟨x, hx, hp⟩

end
end RationalPackingFormula
end ThreeSquares
