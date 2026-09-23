import ThreeSquares.CenterBounds
import ThreeSquares.LocalAlgebra

/-! # Algebraic local geometry around the T configuration

This file uses matrix entries rather than angles. It derives all seven fields
of `LocalConstraints` from vertex containment and four-axis separation, after
exhausting the possible edge axes for each pair.
-/

open scoped NNReal

noncomputable section

namespace ThreeSquares

/-- The orientation-preserving orthogonal matrix with first column `(a,p)`.
For a square, an internal reflection can be absorbed before choosing this
representative, so this is the useful local form. -/
def rotationCoefficients (a p : ℝ) (hunit : a ^ 2 + p ^ 2 = 1) :
    OrthogonalCoefficients where
  a := a
  b := -p
  c := p
  d := a
  first_unit := hunit
  second_unit := by nlinarith
  orthogonal := by ring

@[simp] theorem rotationCoefficients_a (a p : ℝ) (hunit : a ^ 2 + p ^ 2 = 1) :
    (rotationCoefficients a p hunit).a = a := rfl

@[simp] theorem rotationCoefficients_b (a p : ℝ) (hunit : a ^ 2 + p ^ 2 = 1) :
    (rotationCoefficients a p hunit).b = -p := rfl

@[simp] theorem rotationCoefficients_c (a p : ℝ) (hunit : a ^ 2 + p ^ 2 = 1) :
    (rotationCoefficients a p hunit).c = p := rfl

@[simp] theorem rotationCoefficients_d (a p : ℝ) (hunit : a ^ 2 + p ^ 2 = 1) :
    (rotationCoefficients a p hunit).d = a := rfl

/-- The cosine defect is quadratic in the sine entry, with no trigonometric
remainder. -/
theorem rotation_defect_bounds {a p : ℝ} (hunit : a ^ 2 + p ^ 2 = 1)
    (ha : 0 ≤ a) : 0 ≤ 1 - a ∧ 1 - a ≤ p ^ 2 := by
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
  constructor
  · linarith
  · nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (by linarith : 0 ≤ a)]

theorem radius_sq_le_target {r : ℝ≥0} (hr : r ≤ radius) :
    (r : ℝ) ^ 2 ≤ 425 / 256 := by
  have hr' : (r : ℝ) ≤ (radius : ℝ) := by exact_mod_cast hr
  rw [← radius_sq_real]
  nlinarith [r.coe_nonneg, radius.coe_nonneg]

/-- The outer vertex of the left lower square supplies the first disk
inequality.  The nonnegative squared displacement is retained until the last
line, avoiding a Taylor estimate. -/
theorem left_disk_constraint {r : ℝ≥0} {x y a p : ℝ}
    (hunit : a ^ 2 + p ^ 2 = 1)
    (hvertices : VertexInequalities r (point (-1 / 2 + x) (-5 / 16 + y))
      (rotationCoefficients a p hunit)) (hr : r ≤ radius) :
    -2 * x - 13 / 8 * y - 3 / 16 * p ≤ 29 / 16 * (1 - a) := by
  have hv := hvertices.1
  have hr2 := radius_sq_le_target hr
  have hsx := sq_nonneg (x + (1 - a + p) / 2)
  have hsy := sq_nonneg (y + (1 - a - p) / 2)
  norm_num [vertexSquared, rotationCoefficients] at hv
  nlinarith [hunit]

/-- The outer vertex of the right lower square supplies the second disk
inequality. -/
theorem right_disk_constraint {r : ℝ≥0} {x y a p : ℝ}
    (hunit : a ^ 2 + p ^ 2 = 1)
    (hvertices : VertexInequalities r (point (1 / 2 + x) (-5 / 16 + y))
      (rotationCoefficients a p hunit)) (hr : r ≤ radius) :
    2 * x - 13 / 8 * y + 3 / 16 * p ≤ 29 / 16 * (1 - a) := by
  have hv := hvertices.2.2.1
  have hr2 := radius_sq_le_target hr
  have hsx := sq_nonneg (x + (-1 + a + p) / 2)
  have hsy := sq_nonneg (y + (1 - a + p) / 2)
  norm_num [vertexSquared, rotationCoefficients] at hv
  nlinarith [hunit]

/-- The two upper vertices of the horizontal top square give exact linear
supporting inequalities. -/
theorem top_disk_constraints {r : ℝ≥0} {x y : ℝ}
    (hvertices : VertexInequalities r (point x (11 / 16 + y)) identityCoefficients)
    (hr : r ≤ radius) :
    x + 19 / 8 * y ≤ 0 ∧ -x + 19 / 8 * y ≤ 0 := by
  have hvplus := hvertices.2.2.2
  have hvminus := hvertices.2.1
  have hr2 := radius_sq_le_target hr
  norm_num [vertexSquared, identityCoefficients] at hvplus hvminus
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

private theorem square_le_of_abs_le {z ε : ℝ} (hε : 0 ≤ ε) (hz : |z| ≤ ε) :
    z ^ 2 ≤ ε ^ 2 := by
  have hprod := mul_nonneg (sub_nonneg.mpr hz) (add_nonneg (abs_nonneg z) hε)
  nlinarith [sq_abs z]

/-- The four containment-derived fields of `LocalConstraints`, all with the
common algebraic error budget `4 ε²`. -/
theorem local_disk_constraints {r : ℝ≥0}
    {x₁ y₁ x₂ y₂ x₃ y₃ a p b q ε : ℝ}
    (haunit : a ^ 2 + p ^ 2 = 1) (hbunit : b ^ 2 + q ^ 2 = 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (hp : |p| ≤ ε) (hq : |q| ≤ ε)
    (hleft : VertexInequalities r (point (-1 / 2 + x₁) (-5 / 16 + y₁))
      (rotationCoefficients a p haunit))
    (hright : VertexInequalities r (point (1 / 2 + x₂) (-5 / 16 + y₂))
      (rotationCoefficients b q hbunit))
    (htop : VertexInequalities r (point x₃ (11 / 16 + y₃)) identityCoefficients)
    (hr : r ≤ radius) :
    -2 * x₁ - 13 / 8 * y₁ - 3 / 16 * p ≤ 4 * ε ^ 2 ∧
    2 * x₂ - 13 / 8 * y₂ + 3 / 16 * q ≤ 4 * ε ^ 2 ∧
    x₃ + 19 / 8 * y₃ ≤ 4 * ε ^ 2 ∧
    -x₃ + 19 / 8 * y₃ ≤ 4 * ε ^ 2 := by
  have hda := rotation_defect_bounds haunit ha
  have hdb := rotation_defect_bounds hbunit hb
  have hp2 := square_le_of_abs_le hε hp
  have hq2 := square_le_of_abs_le hε hq
  have hl := left_disk_constraint haunit hleft hr
  have hright' := right_disk_constraint hbunit hright hr
  have ht := top_disk_constraints htop hr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg ε]

theorem perturbation_bounds {x₁ y₁ x₂ y₂ x₃ y₃ p q ε : ℝ}
    (h : perturbation x₁ y₁ x₂ y₂ x₃ y₃ p q ≤ ε) :
    |x₁| ≤ ε ∧ |y₁| ≤ ε ∧ |x₂| ≤ ε ∧ |y₂| ≤ ε ∧
    |x₃| ≤ ε ∧ |y₃| ≤ ε ∧ |p| ≤ ε ∧ |q| ≤ ε := by
  simpa only [perturbation, max_le_iff] using h

/-- An edge-axis separation forces at least unit center projection. -/
theorem axis_inequality_projection_abs_ge_one {c d : Plane}
    {A B : OrthogonalCoefficients} {u v : ℝ}
    (h : AxisInequality c d A B u v) (hn : u ^ 2 + v ^ 2 = 1) :
    1 ≤ |u * (d 0 - c 0) + v * (d 1 - c 1)| := by
  have ha := A.projection_l1_ge_one hn
  have hb := B.projection_l1_ge_one hn
  unfold AxisInequality at h
  linarith only [h, ha, hb]

private theorem one_half_perturbation_abs_lt_one {X ε : ℝ}
    (hsmall : ε ≤ 1 / 64) (hX : |X| ≤ 2 * ε) :
    |1 / 2 + X| < 1 := by
  apply abs_lt.mpr
  have hX' := (abs_le.mp hX)
  constructor <;> linarith

private theorem near_horizontal_projection_abs_lt_one {a p X Y ε : ℝ}
    (hunit : a ^ 2 + p ^ 2 = 1) (ha : 0 ≤ a)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 64)
    (hp : |p| ≤ ε) (hX : |X| ≤ 2 * ε) (hY : |Y| ≤ 2 * ε) :
    |a * (1 / 2 + X) + p * (1 + Y)| < 1 := by
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
  have hdx : |1 / 2 + X| ≤ 1 / 2 + 2 * ε := by
    calc
      |1 / 2 + X| ≤ |(1 / 2 : ℝ)| + |X| := abs_add_le _ _
      _ ≤ 1 / 2 + 2 * ε := by norm_num; linarith
  have hdy : |1 + Y| ≤ 1 + 2 * ε := by
    calc
      |1 + Y| ≤ |(1 : ℝ)| + |Y| := abs_add_le _ _
      _ ≤ 1 + 2 * ε := by norm_num; linarith
  have hax : |a| * |1 / 2 + X| ≤ 1 / 2 + 2 * ε := by
    rw [abs_of_nonneg ha]
    calc
      a * |1 / 2 + X| ≤ 1 * (1 / 2 + 2 * ε) :=
        mul_le_mul ha1 hdx (abs_nonneg _) (by positivity)
      _ = 1 / 2 + 2 * ε := one_mul _
  have hpy : |p| * |1 + Y| ≤ ε * (1 + 2 * ε) :=
    mul_le_mul hp hdy (abs_nonneg _) hε
  have htriangle := abs_add_le (a * (1 / 2 + X)) (p * (1 + Y))
  rw [abs_mul, abs_mul] at htriangle
  have hmargin := mul_nonneg hε (sub_nonneg.mpr hsmall)
  nlinarith

private theorem near_vertical_projection_abs_lt_one {a p X Y ε : ℝ}
    (hunit : a ^ 2 + p ^ 2 = 1) (ha : 0 ≤ a)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 64)
    (hp : |p| ≤ ε) (hX : |X| ≤ 2 * ε) (hY : |Y| ≤ 2 * ε) :
    |-p * (1 + X) + a * Y| < 1 := by
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
  have hdx : |1 + X| ≤ 1 + 2 * ε := by
    calc
      |1 + X| ≤ |(1 : ℝ)| + |X| := abs_add_le _ _
      _ ≤ 1 + 2 * ε := by norm_num; linarith
  have hpx : |-p| * |1 + X| ≤ ε * (1 + 2 * ε) := by
    rw [abs_neg]
    exact mul_le_mul hp hdx (abs_nonneg _) hε
  have hay : |a| * |Y| ≤ 2 * ε := by
    rw [abs_of_nonneg ha]
    calc
      a * |Y| ≤ 1 * (2 * ε) := mul_le_mul ha1 hY (abs_nonneg _) (by positivity)
      _ = 2 * ε := one_mul _
  have htriangle := abs_add_le (-p * (1 + X)) (a * Y)
  rw [abs_mul, abs_mul] at htriangle
  have hmargin := mul_nonneg hε (sub_nonneg.mpr hsmall)
  nlinarith

/-- For a lower square and the horizontal top square, the separating axis is
one of the two near-vertical axes.  This exhausts the four edge normals; it
does not assume which pair of edges touches. -/
theorem lower_top_axis_reduction
    {x y x₃ y₃ a p ε : ℝ} (hunit : a ^ 2 + p ^ 2 = 1)
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 64)
    (hx : |x| ≤ ε) (hy : |y| ≤ ε) (hx₃ : |x₃| ≤ ε) (hy₃ : |y₃| ≤ ε)
    (hp : |p| ≤ ε)
    (hsep : FourAxisSeparation
      (point (-1 / 2 + x) (-5 / 16 + y)) (point x₃ (11 / 16 + y₃))
      (rotationCoefficients a p hunit) identityCoefficients) :
    AxisInequality
        (point (-1 / 2 + x) (-5 / 16 + y)) (point x₃ (11 / 16 + y₃))
        (rotationCoefficients a p hunit) identityCoefficients (-p) a ∨
      AxisInequality
        (point (-1 / 2 + x) (-5 / 16 + y)) (point x₃ (11 / 16 + y₃))
        (rotationCoefficients a p hunit) identityCoefficients 0 1 := by
  have hX : |x₃ - x| ≤ 2 * ε := by
    calc
      |x₃ - x| ≤ |x₃| + |x| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  have hY : |y₃ - y| ≤ 2 * ε := by
    calc
      |y₃ - y| ≤ |y₃| + |y| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  have hrot := near_horizontal_projection_abs_lt_one hunit ha hε hsmall hp hX hY
  have hid := one_half_perturbation_abs_lt_one hsmall hX
  rcases hsep with hfirst | hsecond | hidentityFirst | hidentitySecond
  · exfalso
    have h := axis_inequality_projection_abs_ge_one hfirst hunit
    simp only [point_zero, point_one, rotationCoefficients_a, rotationCoefficients_c] at h
    have h' : 1 ≤ |a * (1 / 2 + (x₃ - x)) + p * (1 + (y₃ - y))| := by
      rw [show x₃ - (-1 / 2 + x) = 1 / 2 + (x₃ - x) by ring,
        show 11 / 16 + y₃ - (-5 / 16 + y) = 1 + (y₃ - y) by ring] at h
      exact h
    exact (not_lt_of_ge h') hrot
  · exact Or.inl hsecond
  · exfalso
    have h := axis_inequality_projection_abs_ge_one hidentityFirst
      identityCoefficients.first_unit
    simp only [point_zero, point_one, identityCoefficients] at h
    have h' : 1 ≤ |1 / 2 + (x₃ - x)| := by
      rw [show x₃ - (-1 / 2 + x) = 1 / 2 + (x₃ - x) by ring] at h
      norm_num at h ⊢
      exact h
    exact (not_lt_of_ge h') hid
  · exact Or.inr hidentitySecond

private theorem max_zero_eq_abs_add (z : ℝ) : max z 0 = (|z| + z) / 2 := by
  rcases le_total 0 z with hz | hz
  · rw [max_eq_left hz, abs_of_nonneg hz]
    ring
  · rw [max_eq_right hz, abs_of_nonpos hz]
    ring

private theorem mul_ge_neg_two_sq {u X ε : ℝ} (hε : 0 ≤ ε)
    (hu : |u| ≤ ε) (hX : |X| ≤ 2 * ε) : -2 * ε ^ 2 ≤ u * X := by
  have hprod : |u| * |X| ≤ ε * (2 * ε) :=
    mul_le_mul hu hX (abs_nonneg _) hε
  rw [← abs_mul] at hprod
  nlinarith [neg_le_abs (u * X)]

private theorem lower_top_rotated_vertical_projection_pos
    {a p X Y ε : ℝ} (hunit : a ^ 2 + p ^ 2 = 1)
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 64)
    (hp : |p| ≤ ε) (hX : |X| ≤ 2 * ε) (hY : |Y| ≤ 2 * ε) :
    0 < -p * (1 / 2 + X) + a * (1 + Y) := by
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
  have hp2 := square_le_of_abs_le hε hp
  have haLower : 1 - ε ^ 2 ≤ a := by
    have hd := rotation_defect_bounds hunit ha
    linarith
  have hdx : |1 / 2 + X| ≤ 1 / 2 + 2 * ε := by
    calc
      |1 / 2 + X| ≤ |(1 / 2 : ℝ)| + |X| := abs_add_le _ _
      _ ≤ 1 / 2 + 2 * ε := by norm_num; linarith
  have hpx : |p * (1 / 2 + X)| ≤ ε * (1 / 2 + 2 * ε) := by
    rw [abs_mul]
    exact mul_le_mul hp hdx (abs_nonneg _) hε
  have hay : |a * Y| ≤ 2 * ε := by
    rw [abs_mul, abs_of_nonneg ha]
    calc
      a * |Y| ≤ 1 * (2 * ε) := mul_le_mul ha1 hY (abs_nonneg _) (by positivity)
      _ = 2 * ε := one_mul _
  have hmargin := mul_nonneg hε (sub_nonneg.mpr hsmall)
  have hpLower : -ε * (1 / 2 + 2 * ε) ≤ -p * (1 / 2 + X) := by
    nlinarith [le_abs_self (p * (1 / 2 + X))]
  have hayLower : -2 * ε ≤ a * Y := by nlinarith [neg_le_abs (a * Y)]
  have hquad : ε ^ 2 ≤ ε / 64 := by nlinarith
  nlinarith

/-- The quantitative vertical separation needed for the left-lower/top pair.
Both remaining edge-normal cases from `lower_top_axis_reduction` are handled. -/
theorem lower_top_separation_constraint
    {x y x₃ y₃ a p ε : ℝ} (hunit : a ^ 2 + p ^ 2 = 1)
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 64)
    (hx : |x| ≤ ε) (hy : |y| ≤ ε) (hx₃ : |x₃| ≤ ε) (hy₃ : |y₃| ≤ ε)
    (hp : |p| ≤ ε)
    (hsep : FourAxisSeparation
      (point (-1 / 2 + x) (-5 / 16 + y)) (point x₃ (11 / 16 + y₃))
      (rotationCoefficients a p hunit) identityCoefficients) :
    max p 0 / 2 - 4 * ε ^ 2 ≤ y₃ - y := by
  have hX : |x₃ - x| ≤ 2 * ε := by
    calc
      |x₃ - x| ≤ |x₃| + |x| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  have hY : |y₃ - y| ≤ 2 * ε := by
    calc
      |y₃ - y| ≤ |y₃| + |y| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  have hp2 := square_le_of_abs_le hε hp
  have hdef := rotation_defect_bounds hunit ha
  have hmax : max p 0 = (|p| + p) / 2 := max_zero_eq_abs_add p
  rcases lower_top_axis_reduction hunit ha hε hsmall hx hy hx₃ hy₃ hp hsep with h | h
  · have hpos := lower_top_rotated_vertical_projection_pos
      hunit ha hε hsmall hp hX hY
    unfold AxisInequality at h
    simp only [point_zero, point_one, rotationCoefficients_a, rotationCoefficients_b,
      rotationCoefficients_c, rotationCoefficients_d, identityCoefficients] at h
    norm_num at h
    rw [show -(p * a) + a * p = 0 by ring,
      show p * p + a * a = 1 by nlinarith [hunit], abs_zero, abs_one,
      abs_of_nonneg ha] at h
    rw [show x₃ - (-(1 / 2) + x) = 1 / 2 + (x₃ - x) by ring,
      show 11 / 16 + y₃ - (-(5 / 16) + y) = 1 + (y₃ - y) by ring] at h
    have hpos' : 0 < -(p * (1 / 2 + (x₃ - x))) + a * (1 + (y₃ - y)) := by
      nlinarith [hpos]
    rw [abs_of_pos hpos'] at h
    have hpX := mul_ge_neg_two_sq hε hp hX
    have hYlower : -1 ≤ y₃ - y := by
      have := (abs_le.mp hY).1
      linarith
    have hdefY : -(1 - a) ≤ (1 - a) * (y₃ - y) := by
      nlinarith [mul_nonneg hdef.1 (by linarith : 0 ≤ y₃ - y + 1)]
    have haYUpper : a * (y₃ - y) ≤ (y₃ - y) + (1 - a) := by
      nlinarith only [hdefY]
    have hcoarse : (1 + |p| + a) / 2 ≤
        1 + (y₃ - y) - p / 2 - p * (x₃ - x) := by
      nlinarith only [h, haYUpper]
    rw [hmax]
    nlinarith only [hcoarse, hpX, hdef.2, hp2, neg_le_abs p, sq_nonneg ε]
  · unfold AxisInequality at h
    simp only [point_zero, point_one, rotationCoefficients_a, rotationCoefficients_b,
      rotationCoefficients_c, rotationCoefficients_d, identityCoefficients] at h
    norm_num at h
    rw [abs_of_nonneg ha] at h
    rw [show 11 / 16 + y₃ - (-(5 / 16) + y) = 1 + (y₃ - y) by ring] at h
    have hdy : 0 < 1 + (y₃ - y) := by
      have := (abs_le.mp hY).1
      linarith
    rw [abs_of_pos hdy] at h
    rw [hmax]
    nlinarith [le_abs_self p, neg_le_abs p, abs_nonneg p]

/-- The reflected lower/top pair has the same two-axis reduction. -/
theorem right_lower_top_axis_reduction
    {x y x₃ y₃ b q ε : ℝ} (hunit : b ^ 2 + q ^ 2 = 1)
    (hb : 0 ≤ b) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 64)
    (hx : |x| ≤ ε) (hy : |y| ≤ ε) (hx₃ : |x₃| ≤ ε) (hy₃ : |y₃| ≤ ε)
    (hq : |q| ≤ ε)
    (hsep : FourAxisSeparation
      (point (1 / 2 + x) (-5 / 16 + y)) (point x₃ (11 / 16 + y₃))
      (rotationCoefficients b q hunit) identityCoefficients) :
    AxisInequality
        (point (1 / 2 + x) (-5 / 16 + y)) (point x₃ (11 / 16 + y₃))
        (rotationCoefficients b q hunit) identityCoefficients (-q) b ∨
      AxisInequality
        (point (1 / 2 + x) (-5 / 16 + y)) (point x₃ (11 / 16 + y₃))
        (rotationCoefficients b q hunit) identityCoefficients 0 1 := by
  have hX : |x - x₃| ≤ 2 * ε := by
    calc
      |x - x₃| ≤ |x| + |x₃| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  have hY : |y₃ - y| ≤ 2 * ε := by
    calc
      |y₃ - y| ≤ |y₃| + |y| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  have hunitNeg : b ^ 2 + (-q) ^ 2 = 1 := by nlinarith [hunit]
  have hrot := near_horizontal_projection_abs_lt_one (a := b) (p := -q)
    (X := x - x₃) (Y := y₃ - y) hunitNeg hb hε hsmall
    (by simpa only [abs_neg] using hq) hX hY
  have hid := one_half_perturbation_abs_lt_one hsmall hX
  rcases hsep with hfirst | hsecond | hidentityFirst | hidentitySecond
  · exfalso
    have h := axis_inequality_projection_abs_ge_one hfirst hunit
    simp only [point_zero, point_one, rotationCoefficients_a, rotationCoefficients_c] at h
    have h' : 1 ≤ |b * (1 / 2 + (x - x₃)) + (-q) * (1 + (y₃ - y))| := by
      rw [show x₃ - (1 / 2 + x) = -(1 / 2 + (x - x₃)) by ring,
        show 11 / 16 + y₃ - (-5 / 16 + y) = 1 + (y₃ - y) by ring] at h
      rw [show b * -(1 / 2 + (x - x₃)) + q * (1 + (y₃ - y)) =
        -(b * (1 / 2 + (x - x₃)) + (-q) * (1 + (y₃ - y))) by ring,
        abs_neg] at h
      exact h
    exact (not_lt_of_ge h') hrot
  · exact Or.inl hsecond
  · exfalso
    have h := axis_inequality_projection_abs_ge_one hidentityFirst
      identityCoefficients.first_unit
    simp only [point_zero, point_one, identityCoefficients] at h
    have h' : 1 ≤ |1 / 2 + (x - x₃)| := by
      rw [show x₃ - (1 / 2 + x) = -(1 / 2 + (x - x₃)) by ring] at h
      norm_num at h
      calc
        1 ≤ |x₃ - x + -(1 / 2)| := h
        _ = |1 / 2 + (x - x₃)| := abs_eq_abs.mpr (Or.inr (by ring))
    exact (not_lt_of_ge h') hid
  · exact Or.inr hidentitySecond

/-- The right-lower/top quantitative separation, with the reflected sign
`max (-q) 0` required by `LocalConstraints`. -/
theorem right_lower_top_separation_constraint
    {x y x₃ y₃ b q ε : ℝ} (hunit : b ^ 2 + q ^ 2 = 1)
    (hb : 0 ≤ b) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 64)
    (hx : |x| ≤ ε) (hy : |y| ≤ ε) (hx₃ : |x₃| ≤ ε) (hy₃ : |y₃| ≤ ε)
    (hq : |q| ≤ ε)
    (hsep : FourAxisSeparation
      (point (1 / 2 + x) (-5 / 16 + y)) (point x₃ (11 / 16 + y₃))
      (rotationCoefficients b q hunit) identityCoefficients) :
    max (-q) 0 / 2 - 4 * ε ^ 2 ≤ y₃ - y := by
  have hX : |x - x₃| ≤ 2 * ε := by
    calc
      |x - x₃| ≤ |x| + |x₃| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  have hY : |y₃ - y| ≤ 2 * ε := by
    calc
      |y₃ - y| ≤ |y₃| + |y| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  have hq2 := square_le_of_abs_le hε hq
  have hdef := rotation_defect_bounds hunit hb
  have hunitNeg : b ^ 2 + (-q) ^ 2 = 1 := by nlinarith [hunit]
  have hmax : max (-q) 0 = (|q| - q) / 2 := by
    rw [max_zero_eq_abs_add, abs_neg]
    ring
  rcases right_lower_top_axis_reduction hunit hb hε hsmall hx hy hx₃ hy₃ hq hsep with h | h
  · have hpos := lower_top_rotated_vertical_projection_pos (a := b) (p := -q)
      (X := x - x₃) (Y := y₃ - y) hunitNeg hb hε hsmall
      (by simpa only [abs_neg] using hq) hX hY
    unfold AxisInequality at h
    simp only [point_zero, point_one, rotationCoefficients_a, rotationCoefficients_b,
      rotationCoefficients_c, rotationCoefficients_d, identityCoefficients] at h
    norm_num at h
    rw [show -(q * b) + b * q = 0 by ring,
      show q * q + b * b = 1 by nlinarith [hunit], abs_zero, abs_one,
      abs_of_nonneg hb] at h
    rw [show x₃ - (1 / 2 + x) = -(1 / 2 + (x - x₃)) by ring,
      show 11 / 16 + y₃ - (-(5 / 16) + y) = 1 + (y₃ - y) by ring] at h
    have hpos' : 0 < -((-q) * (1 / 2 + (x - x₃))) + b * (1 + (y₃ - y)) := by
      nlinarith [hpos]
    rw [show -(q * -(1 / 2 + (x - x₃))) + b * (1 + (y₃ - y)) =
      -((-q) * (1 / 2 + (x - x₃))) + b * (1 + (y₃ - y)) by ring,
      abs_of_pos hpos'] at h
    have hqX := mul_ge_neg_two_sq (u := -q) (X := x - x₃) hε
      (by simpa only [abs_neg] using hq) hX
    have hYlower : -1 ≤ y₃ - y := by
      have := (abs_le.mp hY).1
      linarith
    have hdefY : -(1 - b) ≤ (1 - b) * (y₃ - y) := by
      nlinarith [mul_nonneg hdef.1 (by linarith : 0 ≤ y₃ - y + 1)]
    have hbYUpper : b * (y₃ - y) ≤ (y₃ - y) + (1 - b) := by
      nlinarith only [hdefY]
    have hcoarse : (1 + |q| + b) / 2 ≤
        1 + (y₃ - y) + q / 2 + q * (x - x₃) := by
      nlinarith only [h, hbYUpper]
    rw [hmax]
    nlinarith only [hcoarse, hqX, hdef.2, hq2, le_abs_self q, sq_nonneg ε]
  · unfold AxisInequality at h
    simp only [point_zero, point_one, rotationCoefficients_a, rotationCoefficients_b,
      rotationCoefficients_c, rotationCoefficients_d, identityCoefficients] at h
    norm_num at h
    rw [abs_of_nonneg hb] at h
    rw [show 11 / 16 + y₃ - (-(5 / 16) + y) = 1 + (y₃ - y) by ring] at h
    have hdy : 0 < 1 + (y₃ - y) := by
      have := (abs_le.mp hY).1
      linarith
    rw [abs_of_pos hdy] at h
    rw [hmax]
    nlinarith [le_abs_self q, neg_le_abs q, abs_nonneg q]

/-- Between the two lower squares, only the two near-horizontal axes can
separate in the local neighborhood. -/
theorem lower_pair_axis_reduction
    {x₁ y₁ x₂ y₂ a p b q ε : ℝ}
    (haunit : a ^ 2 + p ^ 2 = 1) (hbunit : b ^ 2 + q ^ 2 = 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 64)
    (hx₁ : |x₁| ≤ ε) (hy₁ : |y₁| ≤ ε)
    (hx₂ : |x₂| ≤ ε) (hy₂ : |y₂| ≤ ε)
    (hp : |p| ≤ ε) (hq : |q| ≤ ε)
    (hsep : FourAxisSeparation
      (point (-1 / 2 + x₁) (-5 / 16 + y₁))
      (point (1 / 2 + x₂) (-5 / 16 + y₂))
      (rotationCoefficients a p haunit) (rotationCoefficients b q hbunit)) :
    AxisInequality
        (point (-1 / 2 + x₁) (-5 / 16 + y₁))
        (point (1 / 2 + x₂) (-5 / 16 + y₂))
        (rotationCoefficients a p haunit) (rotationCoefficients b q hbunit) a p ∨
      AxisInequality
        (point (-1 / 2 + x₁) (-5 / 16 + y₁))
        (point (1 / 2 + x₂) (-5 / 16 + y₂))
        (rotationCoefficients a p haunit) (rotationCoefficients b q hbunit) b q := by
  have hX : |x₂ - x₁| ≤ 2 * ε := by
    calc
      |x₂ - x₁| ≤ |x₂| + |x₁| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  have hY : |y₂ - y₁| ≤ 2 * ε := by
    calc
      |y₂ - y₁| ≤ |y₂| + |y₁| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  have hleft := near_vertical_projection_abs_lt_one haunit ha hε hsmall hp hX hY
  have hright := near_vertical_projection_abs_lt_one hbunit hb hε hsmall hq hX hY
  rcases hsep with hfirst | hsecond | hthird | hfourth
  · exact Or.inl hfirst
  · exfalso
    have h := axis_inequality_projection_abs_ge_one hsecond
      (rotationCoefficients a p haunit).second_unit
    simp only [point_zero, point_one, rotationCoefficients_b, rotationCoefficients_d] at h
    have h' : 1 ≤ |-p * (1 + (x₂ - x₁)) + a * (y₂ - y₁)| := by
      rw [show 1 / 2 + x₂ - (-1 / 2 + x₁) = 1 + (x₂ - x₁) by ring,
        show -5 / 16 + y₂ - (-5 / 16 + y₁) = y₂ - y₁ by ring] at h
      exact h
    exact (not_lt_of_ge h') hleft
  · exact Or.inr hthird
  · exfalso
    have h := axis_inequality_projection_abs_ge_one hfourth
      (rotationCoefficients b q hbunit).second_unit
    simp only [point_zero, point_one, rotationCoefficients_b, rotationCoefficients_d] at h
    have h' : 1 ≤ |-q * (1 + (x₂ - x₁)) + b * (y₂ - y₁)| := by
      rw [show 1 / 2 + x₂ - (-1 / 2 + x₁) = 1 + (x₂ - x₁) by ring,
        show -5 / 16 + y₂ - (-5 / 16 + y₁) = y₂ - y₁ by ring] at h
      exact h
    exact (not_lt_of_ge h') hright

private theorem relative_support_lower
    {a p b q ε : ℝ} (haunit : a ^ 2 + p ^ 2 = 1)
    (hbunit : b ^ 2 + q ^ 2 = 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 64) (hp : |p| ≤ ε) (hq : |q| ≤ ε) :
    1 + |q - p| - 7 / 2 * ε ^ 2 ≤
      |a * b + p * q| + |a * q - p * b| := by
  have hda := rotation_defect_bounds haunit ha
  have hdb := rotation_defect_bounds hbunit hb
  have hp2 := square_le_of_abs_le hε hp
  have hq2 := square_le_of_abs_le hε hq
  have hdaε : 1 - a ≤ ε ^ 2 := hda.2.trans hp2
  have hdbε : 1 - b ≤ ε ^ 2 := hdb.2.trans hq2
  have hpq : |p * q| ≤ ε ^ 2 := by
    rw [abs_mul]
    have := mul_le_mul hp hq (abs_nonneg q) hε
    nlinarith
  have hC : 1 - 3 * ε ^ 2 ≤ a * b + p * q := by
    have hab : 1 - (1 - a) - (1 - b) ≤ a * b := by
      nlinarith [mul_nonneg hda.1 hdb.1]
    nlinarith [neg_le_abs (p * q)]
  have he₁ : |(1 - a) * q| ≤ ε ^ 2 * ε := by
    rw [abs_mul, abs_of_nonneg hda.1]
    exact mul_le_mul hdaε hq (abs_nonneg q) (sq_nonneg ε)
  have he₂ : |(1 - b) * p| ≤ ε ^ 2 * ε := by
    rw [abs_mul, abs_of_nonneg hdb.1]
    exact mul_le_mul hdbε hp (abs_nonneg p) (sq_nonneg ε)
  have herror : |(a * q - p * b) - (q - p)| ≤ 2 * ε ^ 3 := by
    rw [show (a * q - p * b) - (q - p) = -(1 - a) * q + (1 - b) * p by ring]
    calc
      |-(1 - a) * q + (1 - b) * p| ≤
          |-(1 - a) * q| + |(1 - b) * p| := abs_add_le _ _
      _ ≤ 2 * ε ^ 3 := by
        rw [show -(1 - a) * q = -((1 - a) * q) by ring, abs_neg]
        nlinarith only [he₁, he₂]
  have hcube : 2 * ε ^ 3 ≤ ε ^ 2 / 2 := by
    have hm := mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hsmall)
    nlinarith
  have hS : |q - p| - ε ^ 2 / 2 ≤ |a * q - p * b| := by
    have ht := abs_sub_le (q - p) (a * q - p * b) 0
    norm_num at ht
    rw [abs_sub_comm (q - p) (a * q - p * b)] at ht
    nlinarith only [ht, herror, hcube]
  nlinarith only [hC, le_abs_self (a * b + p * q), hS]

private theorem lower_pair_horizontal_projection_pos
    {a p D Z ε : ℝ} (hunit : a ^ 2 + p ^ 2 = 1) (ha : 0 ≤ a)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 64)
    (hp : |p| ≤ ε) (hD : |D| ≤ 2 * ε) (hZ : |Z| ≤ 2 * ε) :
    0 < a * (1 + D) + p * Z := by
  have hda := rotation_defect_bounds hunit ha
  have hp2 := square_le_of_abs_le hε hp
  have haLower : 1 - ε ^ 2 ≤ a := by linarith
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
  have haD : |a * D| ≤ 2 * ε := by
    rw [abs_mul, abs_of_nonneg ha]
    exact (mul_le_mul ha1 hD (abs_nonneg D) (by positivity)).trans_eq (one_mul _)
  have hpZ : |p * Z| ≤ 2 * ε ^ 2 := by
    rw [abs_mul]
    have := mul_le_mul hp hZ (abs_nonneg Z) hε
    nlinarith
  have hm := mul_nonneg hε (sub_nonneg.mpr hsmall)
  have hquad : ε ^ 2 ≤ ε / 64 := by nlinarith
  nlinarith [neg_le_abs (a * D), neg_le_abs (p * Z)]

/-- The final separation field of `LocalConstraints`, obtained from either of
the two near-horizontal axes of the lower pair. -/
theorem lower_pair_separation_constraint
    {x₁ y₁ x₂ y₂ a p b q ε : ℝ}
    (haunit : a ^ 2 + p ^ 2 = 1) (hbunit : b ^ 2 + q ^ 2 = 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 64)
    (hx₁ : |x₁| ≤ ε) (hy₁ : |y₁| ≤ ε)
    (hx₂ : |x₂| ≤ ε) (hy₂ : |y₂| ≤ ε)
    (hp : |p| ≤ ε) (hq : |q| ≤ ε)
    (hsep : FourAxisSeparation
      (point (-1 / 2 + x₁) (-5 / 16 + y₁))
      (point (1 / 2 + x₂) (-5 / 16 + y₂))
      (rotationCoefficients a p haunit) (rotationCoefficients b q hbunit)) :
    |q - p| / 2 - 4 * ε ^ 2 ≤ x₂ - x₁ := by
  have hD : |x₂ - x₁| ≤ 2 * ε := by
    calc
      |x₂ - x₁| ≤ |x₂| + |x₁| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  have hZ : |y₂ - y₁| ≤ 2 * ε := by
    calc
      |y₂ - y₁| ≤ |y₂| + |y₁| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  have hsupport := relative_support_lower haunit hbunit ha hb hε hsmall hp hq
  have hDLower : -1 ≤ x₂ - x₁ := by
    have := (abs_le.mp hD).1
    linarith
  rcases lower_pair_axis_reduction haunit hbunit ha hb hε hsmall
      hx₁ hy₁ hx₂ hy₂ hp hq hsep with h | h
  · have hpos := lower_pair_horizontal_projection_pos haunit ha hε hsmall hp hD hZ
    unfold AxisInequality at h
    simp only [point_zero, point_one, rotationCoefficients_a, rotationCoefficients_b,
      rotationCoefficients_c, rotationCoefficients_d] at h
    rw [show a * a + p * p = 1 by nlinarith [haunit],
      show a * -p + p * a = 0 by ring, abs_one, abs_zero,
      show a * -q + p * b = -(a * q - p * b) by ring, abs_neg] at h
    rw [show 1 / 2 + x₂ - (-1 / 2 + x₁) = 1 + (x₂ - x₁) by ring,
      show -5 / 16 + y₂ - (-5 / 16 + y₁) = y₂ - y₁ by ring] at h
    rw [abs_of_pos hpos] at h
    have hpZ : p * (y₂ - y₁) ≤ 2 * ε ^ 2 := by
      have habs : |p * (y₂ - y₁)| ≤ 2 * ε ^ 2 := by
        rw [abs_mul]
        have := mul_le_mul hp hZ (abs_nonneg _) hε
        nlinarith
      exact le_trans (le_abs_self _) habs
    have hdefD : 0 ≤ (1 - a) * (1 + (x₂ - x₁)) :=
      mul_nonneg (rotation_defect_bounds haunit ha).1 (by linarith)
    have hupper : a * (1 + (x₂ - x₁)) + p * (y₂ - y₁) ≤
        1 + (x₂ - x₁) + 2 * ε ^ 2 := by
      nlinarith only [hpZ, hdefD]
    nlinarith only [h, hsupport, hupper, sq_nonneg ε]
  · have hpos := lower_pair_horizontal_projection_pos hbunit hb hε hsmall hq hD hZ
    unfold AxisInequality at h
    simp only [point_zero, point_one, rotationCoefficients_a, rotationCoefficients_b,
      rotationCoefficients_c, rotationCoefficients_d] at h
    rw [show b * a + q * p = a * b + p * q by ring,
      show b * -p + q * a = a * q - p * b by ring,
      show b * b + q * q = 1 by nlinarith [hbunit],
      show b * -q + q * b = 0 by ring, abs_one, abs_zero] at h
    rw [show 1 / 2 + x₂ - (-1 / 2 + x₁) = 1 + (x₂ - x₁) by ring,
      show -5 / 16 + y₂ - (-5 / 16 + y₁) = y₂ - y₁ by ring] at h
    rw [abs_of_pos hpos] at h
    have hqZ : q * (y₂ - y₁) ≤ 2 * ε ^ 2 := by
      have habs : |q * (y₂ - y₁)| ≤ 2 * ε ^ 2 := by
        rw [abs_mul]
        have := mul_le_mul hq hZ (abs_nonneg _) hε
        nlinarith
      exact le_trans (le_abs_self _) habs
    have hdefD : 0 ≤ (1 - b) * (1 + (x₂ - x₁)) :=
      mul_nonneg (rotation_defect_bounds hbunit hb).1 (by linarith)
    have hupper : b * (1 + (x₂ - x₁)) + q * (y₂ - y₁) ≤
        1 + (x₂ - x₁) + 2 * ε ^ 2 := by
      nlinarith only [hqZ, hdefD]
    nlinarith only [h, hsupport, hupper, sq_nonneg ε]

/-- All seven local algebra constraints follow from the actual vertex and
four-axis packing constraints in the matrix-entry neighborhood. -/
theorem local_constraints_of_geometry {r : ℝ≥0}
    {x₁ y₁ x₂ y₂ x₃ y₃ a p b q ε : ℝ}
    (haunit : a ^ 2 + p ^ 2 = 1) (hbunit : b ^ 2 + q ^ 2 = 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 64)
    (hpert : perturbation x₁ y₁ x₂ y₂ x₃ y₃ p q ≤ ε)
    (hleft : VertexInequalities r (point (-1 / 2 + x₁) (-5 / 16 + y₁))
      (rotationCoefficients a p haunit))
    (hright : VertexInequalities r (point (1 / 2 + x₂) (-5 / 16 + y₂))
      (rotationCoefficients b q hbunit))
    (htop : VertexInequalities r (point x₃ (11 / 16 + y₃)) identityCoefficients)
    (h₁₂ : FourAxisSeparation
      (point (-1 / 2 + x₁) (-5 / 16 + y₁))
      (point (1 / 2 + x₂) (-5 / 16 + y₂))
      (rotationCoefficients a p haunit) (rotationCoefficients b q hbunit))
    (h₁₃ : FourAxisSeparation
      (point (-1 / 2 + x₁) (-5 / 16 + y₁)) (point x₃ (11 / 16 + y₃))
      (rotationCoefficients a p haunit) identityCoefficients)
    (h₂₃ : FourAxisSeparation
      (point (1 / 2 + x₂) (-5 / 16 + y₂)) (point x₃ (11 / 16 + y₃))
      (rotationCoefficients b q hbunit) identityCoefficients)
    (hr : r ≤ radius) :
    LocalConstraints (4 * ε ^ 2) x₁ y₁ x₂ y₂ x₃ y₃ p q := by
  obtain ⟨hx₁, hy₁, hx₂, hy₂, hx₃, hy₃, hp, hq⟩ := perturbation_bounds hpert
  obtain ⟨hd₁, hd₂, hd₃, hd₄⟩ := local_disk_constraints
    haunit hbunit ha hb hε hp hq hleft hright htop hr
  exact
    { disk₁ := hd₁
      disk₂ := hd₂
      disk₃plus := hd₃
      disk₃minus := hd₄
      separation₁₂ := lower_pair_separation_constraint haunit hbunit ha hb hε hsmall
        hx₁ hy₁ hx₂ hy₂ hp hq h₁₂
      separation₁₃ := lower_top_separation_constraint haunit ha hε hsmall
        hx₁ hy₁ hx₃ hy₃ hp h₁₃
      separation₂₃ := right_lower_top_separation_constraint hbunit hb hε hsmall
        hx₂ hy₂ hx₃ hy₃ hq h₂₃ }

/-- Local rigidity for actual squares in the normalized matrix-entry form. -/
theorem local_geometry_rigidity {r : ℝ≥0}
    {x₁ y₁ x₂ y₂ x₃ y₃ a p b q : ℝ}
    (haunit : a ^ 2 + p ^ 2 = 1) (hbunit : b ^ 2 + q ^ 2 = 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsmall : perturbation x₁ y₁ x₂ y₂ x₃ y₃ p q ≤ 1 / 64)
    (hleft : VertexInequalities r (point (-1 / 2 + x₁) (-5 / 16 + y₁))
      (rotationCoefficients a p haunit))
    (hright : VertexInequalities r (point (1 / 2 + x₂) (-5 / 16 + y₂))
      (rotationCoefficients b q hbunit))
    (htop : VertexInequalities r (point x₃ (11 / 16 + y₃)) identityCoefficients)
    (h₁₂ : FourAxisSeparation
      (point (-1 / 2 + x₁) (-5 / 16 + y₁))
      (point (1 / 2 + x₂) (-5 / 16 + y₂))
      (rotationCoefficients a p haunit) (rotationCoefficients b q hbunit))
    (h₁₃ : FourAxisSeparation
      (point (-1 / 2 + x₁) (-5 / 16 + y₁)) (point x₃ (11 / 16 + y₃))
      (rotationCoefficients a p haunit) identityCoefficients)
    (h₂₃ : FourAxisSeparation
      (point (1 / 2 + x₂) (-5 / 16 + y₂)) (point x₃ (11 / 16 + y₃))
      (rotationCoefficients b q hbunit) identityCoefficients)
    (hr : r ≤ radius) :
    x₁ = 0 ∧ y₁ = 0 ∧ x₂ = 0 ∧ y₂ = 0 ∧ x₃ = 0 ∧ y₃ = 0 ∧
      p = 0 ∧ q = 0 ∧ a = 1 ∧ b = 1 := by
  let ε := perturbation x₁ y₁ x₂ y₂ x₃ y₃ p q
  have hconstraints : LocalConstraints (4 * ε ^ 2) x₁ y₁ x₂ y₂ x₃ y₃ p q :=
    local_constraints_of_geometry haunit hbunit ha hb (perturbation_nonneg ..)
      hsmall le_rfl hleft hright htop h₁₂ h₁₃ h₂₃ hr
  have hzero := local_algebra_rigidity_four hsmall hconstraints
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hzero
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by nlinarith, by nlinarith⟩

/-- The actual local packing constraints force the candidate radius.  This is
the local lower bound that the global certificate must eventually reach. -/
theorem local_geometry_radius_lower_bound {r : ℝ≥0}
    {x₁ y₁ x₂ y₂ x₃ y₃ a p b q : ℝ}
    (haunit : a ^ 2 + p ^ 2 = 1) (hbunit : b ^ 2 + q ^ 2 = 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsmall : perturbation x₁ y₁ x₂ y₂ x₃ y₃ p q ≤ 1 / 64)
    (hleft : VertexInequalities r (point (-1 / 2 + x₁) (-5 / 16 + y₁))
      (rotationCoefficients a p haunit))
    (hright : VertexInequalities r (point (1 / 2 + x₂) (-5 / 16 + y₂))
      (rotationCoefficients b q hbunit))
    (htop : VertexInequalities r (point x₃ (11 / 16 + y₃)) identityCoefficients)
    (h₁₂ : FourAxisSeparation
      (point (-1 / 2 + x₁) (-5 / 16 + y₁))
      (point (1 / 2 + x₂) (-5 / 16 + y₂))
      (rotationCoefficients a p haunit) (rotationCoefficients b q hbunit))
    (h₁₃ : FourAxisSeparation
      (point (-1 / 2 + x₁) (-5 / 16 + y₁)) (point x₃ (11 / 16 + y₃))
      (rotationCoefficients a p haunit) identityCoefficients)
    (h₂₃ : FourAxisSeparation
      (point (1 / 2 + x₂) (-5 / 16 + y₂)) (point x₃ (11 / 16 + y₃))
      (rotationCoefficients b q hbunit) identityCoefficients) : radius ≤ r := by
  by_contra hn
  have hr : r ≤ radius := le_of_lt (lt_of_not_ge hn)
  obtain ⟨hx₁, hy₁, hx₂, hy₂, hx₃, hy₃, hp, hq, ha', hb'⟩ :=
    local_geometry_rigidity haunit hbunit ha hb hsmall hleft hright htop h₁₂ h₁₃ h₂₃ hr
  subst x₁
  subst y₁
  subst x₂
  subst y₂
  subst x₃
  subst y₃
  subst p
  subst q
  subst a
  subst b
  have hv := hleft.1
  norm_num [vertexSquared, rotationCoefficients] at hv
  have hr' : (r : ℝ) < (radius : ℝ) := by exact_mod_cast lt_of_not_ge hn
  have hr2 : (r : ℝ) ^ 2 < 425 / 256 := by
    nlinarith [radius_sq_real, r.coe_nonneg, radius.coe_nonneg]
  nlinarith

end ThreeSquares
