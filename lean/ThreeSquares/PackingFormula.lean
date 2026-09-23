import ThreeSquares.PackingSyntax
import ThreeSquares.EdgeConstraints

/-! # Encoding the normalized square-packing constraints for the checker

Variables 0--5 are the three centers, 6--13 the entries of the second and
third orthogonal matrices, and 14 the squared radius. The first frame is
the identity. This module proves that every normalized FC packing satisfies
the encoded formula; no certificate of global exclusion is supplied here.
-/

open scoped NNReal

namespace ThreeSquares
namespace PackingFormula

noncomputable def assignment {r : ℝ≥0} (P : EdgeConstraintPacking 3 r) : Fin 15 → ℝ :=
  ![P.centers 0 0, P.centers 0 1, P.centers 1 0, P.centers 1 1,
    P.centers 2 0, P.centers 2 1,
    (P.coefficients 1).a, (P.coefficients 1).b, (P.coefficients 1).c, (P.coefficients 1).d,
    (P.coefficients 2).a, (P.coefficients 2).b, (P.coefficients 2).c, (P.coefficients 2).d,
    (r : ℝ) ^ 2]

private theorem eval_centers {r : ℝ≥0} (P : EdgeConstraintPacking 3 r) (i : Fin 3) :
    (centerX i).eval (assignment P) = P.centers i 0 ∧
      (centerY i).eval (assignment P) = P.centers i 1 := by
  fin_cases i <;> simp [centerX, centerY, IntervalExpr.eval, assignment]

private theorem eval_frame {r : ℝ≥0} (P : EdgeConstraintPacking 3 r)
    (hP : P.coefficients 0 = identityCoefficients) (i : Fin 3) :
    (frame i).a.eval (assignment P) = (P.coefficients i).a ∧
    (frame i).b.eval (assignment P) = (P.coefficients i).b ∧
    (frame i).c.eval (assignment P) = (P.coefficients i).c ∧
    (frame i).d.eval (assignment P) = (P.coefficients i).d := by
  fin_cases i <;> simp [frame, IntervalExpr.eval, assignment, hP, identityCoefficients]

theorem vertex_eval {r : ℝ≥0} (P : EdgeConstraintPacking 3 r)
    (hP : P.coefficients 0 = identityCoefficients) (i : Fin 3) (x y : ℚ) :
    (vertex i x y).eval (assignment P) = vertexSquared (P.centers i) (P.coefficients i) x y := by
  have hc := eval_centers P i
  have hf := eval_frame P hP i
  simp only [vertex, IntervalExpr.eval, hc.1, hc.2, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2,
    vertexSquared]

theorem orthogonal_holds {r : ℝ≥0} (P : EdgeConstraintPacking 3 r)
    (hP : P.coefficients 0 = identityCoefficients) (i : Fin 3) :
    (orthogonal i).Holds (assignment P) := by
  have hf := eval_frame P hP i
  simp only [orthogonal, eq, sub, IntervalFormula.Holds, IntervalExpr.eval,
    hf.1, hf.2.1, hf.2.2.1, hf.2.2.2, Rat.cast_one, Rat.cast_zero]
  exact ⟨by linarith [(P.coefficients i).first_unit],
    by linarith [(P.coefficients i).second_unit], by linarith [(P.coefficients i).orthogonal]⟩

theorem vertices_holds {r : ℝ≥0} (P : EdgeConstraintPacking 3 r)
    (hP : P.coefficients 0 = identityCoefficients) (i : Fin 3) :
    (vertices i).Holds (assignment P) := by
  have h := P.vertices i
  change VertexInequalities r (P.centers i) (P.coefficients i) at h
  have hr : assignment P 14 = (r : ℝ) ^ 2 := rfl
  simp only [vertices, le, sub, IntervalFormula.Holds, IntervalExpr.eval, vertex_eval P hP, hr]
  norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, neg_div]
  rcases h with ⟨h1, h2, h3, h4⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem axis_holds_iff {r : ℝ≥0} (P : EdgeConstraintPacking 3 r)
    (hP : P.coefficients 0 = identityCoefficients) (i j : Fin 3) (u v : E) :
    (axis i j u v).Holds (assignment P) ↔
      AxisInequality (P.centers i) (P.centers j) (P.coefficients i) (P.coefficients j)
        (u.eval (assignment P)) (v.eval (assignment P)) := by
  have hc := eval_centers P i
  have hd := eval_centers P j
  have hf := eval_frame P hP i
  have hg := eval_frame P hP j
  simp only [axis, le, sub, width, IntervalFormula.Holds, IntervalExpr.eval,
    hc.1, hc.2, hd.1, hd.2, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2,
    hg.1, hg.2.1, hg.2.2.1, hg.2.2.2, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
    AxisInequality, ← sub_eq_add_neg]
  constructor <;> intro h <;> linarith only [h]

theorem pair_holds {r : ℝ≥0} (P : EdgeConstraintPacking 3 r)
    (hP : P.coefficients 0 = identityCoefficients) (i j : Fin 3) (hij : i < j) :
    (pair i j).Holds (assignment P) := by
  have hf := eval_frame P hP i
  have hg := eval_frame P hP j
  simpa only [pair, IntervalFormula.Holds, axis_holds_iff P hP,
    hf.1, hf.2.1, hf.2.2.1, hf.2.2.2, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2,
    FourAxisSeparation] using P.separations i j hij

theorem formula_holds {r : ℝ≥0} (P : EdgeConstraintPacking 3 r)
    (hP : P.coefficients 0 = identityCoefficients) : formula.Holds (assignment P) := by
  exact ⟨orthogonal_holds P hP 0, orthogonal_holds P hP 1, orthogonal_holds P hP 2,
    vertices_holds P hP 0, vertices_holds P hP 1, vertices_holds P hP 2,
    pair_holds P hP 0 1 (by decide), pair_holds P hP 0 2 (by decide),
    pair_holds P hP 1 2 (by decide)⟩

theorem certificate_localizes_packing {r : ℝ≥0} (P : EdgeConstraintPacking 3 r)
    (hP : P.coefficients 0 = identityCoefficients) (B : RationalBox 15)
    (t : IntervalCertificate 15) (hcheck : t.check formula B = true)
    (hB : B.Contains (assignment P)) :
    ∃ C ∈ t.residuals B, C.Contains (assignment P) :=
  t.check_sound formula hcheck hB (formula_holds P hP)

end PackingFormula
end ThreeSquares
