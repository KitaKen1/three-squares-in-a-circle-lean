import ThreeSquares.RationalPackingSyntax
import ThreeSquares.SubcriticalRationalPacking
import ThreeSquares.CenterBounds

/-! # Semantics of the eight-variable rational packing formula

The formulas in `RationalPackingSyntax` have all rational-rotation
denominators cleared. This file proves that every normalized subcritical FC
packing satisfies those formulas in the contracted eight-dimensional box.
-/

open scoped NNReal
open SquarePacking

namespace ThreeSquares
namespace RationalPackingFormula

noncomputable def assignment (P : SubcriticalRationalRotationPacking 3) : Fin 8 → ℝ :=
  ![P.centers 0 0, P.centers 0 1, P.centers 1 0, P.centers 1 1,
    P.centers 2 0, P.centers 2 1, P.t 1, P.t 2]

private theorem eval_centers (P : SubcriticalRationalRotationPacking 3) (i : Fin 3) :
    (centerX i).eval (assignment P) = P.centers i 0 ∧
      (centerY i).eval (assignment P) = P.centers i 1 := by
  fin_cases i <;> simp [centerX, centerY, IntervalExpr.eval, assignment]

private theorem eval_parameter (P : SubcriticalRationalRotationPacking 3)
    (hP : P.t 0 = 0) (i : Fin 3) :
    (parameter i).eval (assignment P) = P.t i := by
  fin_cases i <;> simp [parameter, IntervalExpr.eval, assignment, hP]

private theorem eval_denominator (P : SubcriticalRationalRotationPacking 3)
    (hP : P.t 0 = 0) (i : Fin 3) :
    (denominator i).eval (assignment P) = 1 + (P.t i) ^ 2 := by
  simp [denominator, IntervalExpr.eval, eval_parameter P hP]

private theorem eval_cosineNumerator (P : SubcriticalRationalRotationPacking 3)
    (hP : P.t 0 = 0) (i : Fin 3) :
    (cosineNumerator i).eval (assignment P) = 1 - (P.t i) ^ 2 := by
  simp only [cosineNumerator, sub, IntervalExpr.eval, eval_parameter P hP, Rat.cast_one]
  ring

private theorem eval_sineNumerator (P : SubcriticalRationalRotationPacking 3)
    (hP : P.t 0 = 0) (i : Fin 3) :
    (sineNumerator i).eval (assignment P) = 2 * P.t i := by
  simp [sineNumerator, IntervalExpr.eval, eval_parameter P hP]

theorem vertexNumerator_eval (P : SubcriticalRationalRotationPacking 3)
    (hP : P.t 0 = 0) (i : Fin 3) (x y : ℚ) :
    (vertexNumerator i x y).eval (assignment P) =
      (1 + (P.t i) ^ 2) ^ 2 *
        vertexSquared (P.centers i) (rationalRotationCoefficients (P.t i)) x y := by
  have hc := eval_centers P i
  have ht := eval_parameter P hP i
  simp only [vertexNumerator, denominator, cosineNumerator, sineNumerator, sub,
    IntervalExpr.eval, hc.1, hc.2, ht, vertexSquared, rationalRotationCoefficients,
    rotationCoefficients_a, rotationCoefficients_b, rotationCoefficients_c,
    rotationCoefficients_d, rationalCos, rationalSin]
  have hd : 1 + (P.t i) ^ 2 ≠ 0 := ne_of_gt (rational_denominator_pos (P.t i))
  field_simp [hd]
  ring

theorem parameterBounds_holds (P : SubcriticalRationalRotationPacking 3)
    (hP : P.t 0 = 0) (i : Fin 3) :
    (parameterBounds i).Holds (assignment P) := by
  simp only [parameterBounds, sub, IntervalFormula.Holds, IntervalExpr.eval,
    eval_parameter P hP, Rat.cast_one]
  exact ⟨by linarith [P.t_nonneg i], by linarith [P.t_le_one i]⟩

theorem strictVertex_holds (P : SubcriticalRationalRotationPacking 3)
    (hP : P.t 0 = 0) (i : Fin 3) (x y : ℚ)
    (hvertex : vertexSquared (P.centers i) (rationalRotationCoefficients (P.t i))
      x y < 425 / 256) :
    (strictVertex i x y).Holds (assignment P) := by
  have hd : 0 < (1 + (P.t i) ^ 2) ^ 2 := sq_pos_of_pos (rational_denominator_pos (P.t i))
  simp only [strictVertex, sub, IntervalFormula.Holds, IntervalExpr.eval,
    vertexNumerator_eval P hP, eval_denominator P hP]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  nlinarith

theorem vertices_holds (P : SubcriticalRationalRotationPacking 3)
    (hP : P.t 0 = 0) (i : Fin 3) :
    (vertices i).Holds (assignment P) := by
  rcases P.vertices i with ⟨h₁, h₂, h₃, h₄⟩
  constructor
  · apply strictVertex_holds P hP i (-1 / 2) (-1 / 2)
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, neg_div]
    simpa only [neg_div] using h₁
  constructor
  · apply strictVertex_holds P hP i (-1 / 2) (1 / 2)
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, neg_div]
    simpa only [neg_div] using h₂
  constructor
  · apply strictVertex_holds P hP i (1 / 2) (-1 / 2)
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, neg_div]
    simpa only [neg_div] using h₃
  · apply strictVertex_holds P hP i (1 / 2) (1 / 2)
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, neg_div]
    exact h₄

private theorem divided_axis_inequality_iff_cleared
    {di dj dk ci si cj sj u v dx dy : ℝ}
    (hdi : 0 < di) (hdj : 0 < dj) (hdk : 0 < dk) :
    ((|(u / dk) * (ci / di) + (v / dk) * (si / di)| +
        |(u / dk) * (-si / di) + (v / dk) * (ci / di)| +
        |(u / dk) * (cj / dj) + (v / dk) * (sj / dj)| +
        |(u / dk) * (-sj / dj) + (v / dk) * (cj / dj)|) / 2 ≤
        |(u / dk) * dx + (v / dk) * dy|) ↔
      (|u * ci + v * si| + |-u * si + v * ci|) * dj +
          (|u * cj + v * sj| + |-u * sj + v * cj|) * di ≤
        2 * |u * dx + v * dy| * di * dj := by
  have hdki : 0 < dk * di := mul_pos hdk hdi
  have hdkj : 0 < dk * dj := mul_pos hdk hdj
  have hscale : 0 < 2 * dk * di * dj := by positivity
  have hi₁ : (u / dk) * (ci / di) + (v / dk) * (si / di) =
      (u * ci + v * si) / (dk * di) := by
    field_simp [ne_of_gt hdi, ne_of_gt hdk]
  have hi₂ : (u / dk) * (-si / di) + (v / dk) * (ci / di) =
      (-u * si + v * ci) / (dk * di) := by
    field_simp [ne_of_gt hdi, ne_of_gt hdk]
  have hj₁ : (u / dk) * (cj / dj) + (v / dk) * (sj / dj) =
      (u * cj + v * sj) / (dk * dj) := by
    field_simp [ne_of_gt hdj, ne_of_gt hdk]
  have hj₂ : (u / dk) * (-sj / dj) + (v / dk) * (cj / dj) =
      (-u * sj + v * cj) / (dk * dj) := by
    field_simp [ne_of_gt hdj, ne_of_gt hdk]
  have hp : (u / dk) * dx + (v / dk) * dy = (u * dx + v * dy) / dk := by
    field_simp [ne_of_gt hdk]
  rw [hi₁, hi₂, hj₁, hj₂, hp, abs_div, abs_div, abs_div, abs_div, abs_div,
    abs_of_pos hdki, abs_of_pos hdkj, abs_of_pos hdk]
  have hleft :
      ((|u * ci + v * si| / (dk * di) + |-u * si + v * ci| / (dk * di) +
          |u * cj + v * sj| / (dk * dj) + |-u * sj + v * cj| / (dk * dj)) / 2) =
        ((|u * ci + v * si| + |-u * si + v * ci|) * dj +
          (|u * cj + v * sj| + |-u * sj + v * cj|) * di) /
            (2 * dk * di * dj) := by
    field_simp [ne_of_gt hdi, ne_of_gt hdj, ne_of_gt hdk]
    ring
  have hright : |u * dx + v * dy| / dk =
      (2 * |u * dx + v * dy| * di * dj) / (2 * dk * di * dj) := by
    field_simp [ne_of_gt hdi, ne_of_gt hdj, ne_of_gt hdk]
  rw [hleft, hright, div_le_div_iff_of_pos_right hscale]

private theorem widthNumerator_eval (P : SubcriticalRationalRotationPacking 3)
    (hP : P.t 0 = 0) (i : Fin 3) (u v : E) :
    (widthNumerator i u v).eval (assignment P) =
      |u.eval (assignment P) * (1 - (P.t i) ^ 2) +
        v.eval (assignment P) * (2 * P.t i)| +
      |-u.eval (assignment P) * (2 * P.t i) +
        v.eval (assignment P) * (1 - (P.t i) ^ 2)| := by
  simp only [widthNumerator, IntervalExpr.eval, eval_cosineNumerator P hP,
    eval_sineNumerator P hP]
  ring_nf

private theorem centerProjectionNumerator_eval
    (P : SubcriticalRationalRotationPacking 3) (i j : Fin 3) (u v : E) :
    (centerProjectionNumerator i j u v).eval (assignment P) =
      u.eval (assignment P) * (P.centers j 0 - P.centers i 0) +
        v.eval (assignment P) * (P.centers j 1 - P.centers i 1) := by
  have hi := eval_centers P i
  have hj := eval_centers P j
  simp only [centerProjectionNumerator, sub, IntervalExpr.eval, hi.1, hi.2, hj.1, hj.2]
  ring

private theorem axis_formula_iff_cleared
    (P : SubcriticalRationalRotationPacking 3) (hP : P.t 0 = 0)
    (i j : Fin 3) (u v : E) :
    (axis i j u v).Holds (assignment P) ↔
      (|u.eval (assignment P) * (1 - (P.t i) ^ 2) +
          v.eval (assignment P) * (2 * P.t i)| +
        |-u.eval (assignment P) * (2 * P.t i) +
          v.eval (assignment P) * (1 - (P.t i) ^ 2)|) *
          (1 + (P.t j) ^ 2) +
        (|u.eval (assignment P) * (1 - (P.t j) ^ 2) +
          v.eval (assignment P) * (2 * P.t j)| +
        |-u.eval (assignment P) * (2 * P.t j) +
          v.eval (assignment P) * (1 - (P.t j) ^ 2)|) *
          (1 + (P.t i) ^ 2) ≤
        2 * |u.eval (assignment P) * (P.centers j 0 - P.centers i 0) +
          v.eval (assignment P) * (P.centers j 1 - P.centers i 1)| *
          (1 + (P.t i) ^ 2) * (1 + (P.t j) ^ 2) := by
  simp only [axis, le, sub, IntervalFormula.Holds, IntervalExpr.eval,
    widthNumerator_eval P hP, centerProjectionNumerator_eval P,
    eval_denominator P hP, Rat.cast_ofNat]
  constructor <;> intro h <;> linarith only [h]

theorem firstAxis_holds_iff (P : SubcriticalRationalRotationPacking 3)
    (hP : P.t 0 = 0) (i j k : Fin 3) :
    (axis i j (cosineNumerator k) (sineNumerator k)).Holds (assignment P) ↔
      AxisInequality (P.centers i) (P.centers j)
        (rationalRotationCoefficients (P.t i))
        (rationalRotationCoefficients (P.t j))
        (rationalRotationCoefficients (P.t k)).a
        (rationalRotationCoefficients (P.t k)).c := by
  have hdi := rational_denominator_pos (P.t i)
  have hdj := rational_denominator_pos (P.t j)
  have hdk := rational_denominator_pos (P.t k)
  have hclear := divided_axis_inequality_iff_cleared
    (di := 1 + (P.t i) ^ 2) (dj := 1 + (P.t j) ^ 2)
    (dk := 1 + (P.t k) ^ 2)
    (ci := 1 - (P.t i) ^ 2) (si := 2 * P.t i)
    (cj := 1 - (P.t j) ^ 2) (sj := 2 * P.t j)
    (u := 1 - (P.t k) ^ 2) (v := 2 * P.t k)
    (dx := P.centers j 0 - P.centers i 0)
    (dy := P.centers j 1 - P.centers i 1) hdi hdj hdk
  unfold AxisInequality at hclear ⊢
  simp only [rationalRotationCoefficients, rotationCoefficients_a,
    rotationCoefficients_b, rotationCoefficients_c, rotationCoefficients_d,
    rationalCos, rationalSin] at hclear ⊢
  rw [axis_formula_iff_cleared P hP]
  rw [eval_cosineNumerator P hP, eval_sineNumerator P hP]
  simpa only [neg_div] using hclear.symm

theorem secondAxis_holds_iff (P : SubcriticalRationalRotationPacking 3)
    (hP : P.t 0 = 0) (i j k : Fin 3) :
    (axis i j (.neg (sineNumerator k)) (cosineNumerator k)).Holds (assignment P) ↔
      AxisInequality (P.centers i) (P.centers j)
        (rationalRotationCoefficients (P.t i))
        (rationalRotationCoefficients (P.t j))
        (rationalRotationCoefficients (P.t k)).b
        (rationalRotationCoefficients (P.t k)).d := by
  have hdi := rational_denominator_pos (P.t i)
  have hdj := rational_denominator_pos (P.t j)
  have hdk := rational_denominator_pos (P.t k)
  have hclear := divided_axis_inequality_iff_cleared
    (di := 1 + (P.t i) ^ 2) (dj := 1 + (P.t j) ^ 2)
    (dk := 1 + (P.t k) ^ 2)
    (ci := 1 - (P.t i) ^ 2) (si := 2 * P.t i)
    (cj := 1 - (P.t j) ^ 2) (sj := 2 * P.t j)
    (u := -(2 * P.t k)) (v := 1 - (P.t k) ^ 2)
    (dx := P.centers j 0 - P.centers i 0)
    (dy := P.centers j 1 - P.centers i 1) hdi hdj hdk
  unfold AxisInequality at hclear ⊢
  simp only [rationalRotationCoefficients, rotationCoefficients_a,
    rotationCoefficients_b, rotationCoefficients_c, rotationCoefficients_d,
    rationalCos, rationalSin] at hclear ⊢
  rw [axis_formula_iff_cleared P hP]
  simp only [IntervalExpr.eval, eval_cosineNumerator P hP, eval_sineNumerator P hP]
  simpa only [neg_div] using hclear.symm

theorem pair_holds (P : SubcriticalRationalRotationPacking 3)
    (hP : P.t 0 = 0) (i j : Fin 3) (hij : i < j) :
    (pair i j).Holds (assignment P) := by
  simpa only [pair, IntervalFormula.Holds, firstAxis_holds_iff P hP,
    secondAxis_holds_iff P hP, FourAxisSeparation] using P.separations i j hij

theorem formula_holds (P : SubcriticalRationalRotationPacking 3)
    (hP : P.t 0 = 0) : formula.Holds (assignment P) := by
  exact ⟨parameterBounds_holds P hP 1, parameterBounds_holds P hP 2,
    vertices_holds P hP 0, vertices_holds P hP 1, vertices_holds P hP 2,
    pair_holds P hP 0 1 (by decide), pair_holds P hP 0 2 (by decide),
    pair_holds P hP 1 2 (by decide)⟩

theorem assignment_in_initialBox {r : ℝ≥0} (P : RationalRotationPacking 3 r)
    (hr : r < radius) : initialBox.Contains (assignment (P.toSubcritical hr)) := by
  have hc (i : Fin 3) (k : Fin 2) :
      -(11 / 16) ≤ P.centers i k ∧ P.centers i k ≤ 11 / 16 :=
    abs_le.mp (le_of_lt (center_coordinate_lt_eleven_sixteenths (P.vertices i) hr k))
  have ht (i : Fin 3) : 0 ≤ P.t i ∧ P.t i ≤ 1 :=
    ⟨P.t_nonneg i, P.t_le_one i⟩
  intro i
  fin_cases i <;> norm_num [initialBox, RationalInterval.Contains, assignment,
    RationalRotationPacking.toSubcritical]
  · exact hc 0 0
  · exact hc 0 1
  · exact hc 1 0
  · exact hc 1 1
  · exact hc 2 0
  · exact hc 2 1
  · exact ht 1
  · exact ht 2

/-- Every FC packing below the candidate radius produces a solution of the
denominator-free eight-variable formula in its explicit initial box. -/
theorem smaller_fc_packing_has_eight_variable_assignment {r : ℝ≥0}
    (hr : r < radius) (h : Nonempty (Packing 3 UnitSquare (Circle r))) :
    ∃ x : Fin 8 → ℝ, initialBox.Contains x ∧ formula.Holds x := by
  obtain ⟨P, hP⟩ := (normalized_rational_rotation_packing_iff 3 r 0).mpr h
  let Q := P.toSubcritical hr
  exact ⟨assignment Q, assignment_in_initialBox P hr, formula_holds Q hP⟩

theorem certificate_localizes_smaller_fc_packing (t : IntervalCertificate 8)
    (hcheck : t.check formula initialBox = true) {r : ℝ≥0} (hr : r < radius)
    (h : Nonempty (Packing 3 UnitSquare (Circle r))) :
    ∃ x : Fin 8 → ℝ, ∃ C ∈ t.residuals initialBox,
      C.Contains x ∧ formula.Holds x := by
  obtain ⟨x, hx, hp⟩ := smaller_fc_packing_has_eight_variable_assignment hr h
  obtain ⟨C, hC, hCx⟩ := t.check_sound formula hcheck hx hp
  exact ⟨x, C, hC, hCx, hp⟩

/-- A fully checked empty certificate over the eight-variable formula would
close the remaining arbitrary-rotation lower bound. -/
theorem global_lower_bound_of_empty_eight_variable_certificate
    (t : IntervalCertificate 8) (hcheck : t.check formula initialBox = true)
    (hempty : t.residuals initialBox = []) : GlobalLowerBound := by
  intro r hr
  by_contra hn
  exact t.exclude_sound formula hcheck hempty
    (smaller_fc_packing_has_eight_variable_assignment (lt_of_not_ge hn) hr)

end RationalPackingFormula
end ThreeSquares
