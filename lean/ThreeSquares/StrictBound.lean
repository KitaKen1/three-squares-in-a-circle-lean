import ThreeSquares.BranchSymmetry

/-! # Strict form of center elimination

Every subcritical FC packing has all twelve vertices strictly inside the
candidate squared radius. Since the certificate weights are nonnegative and
sum to one, their weighted vertex mean is also strictly below the candidate.
The completing-square identity then gives a strict upper bound on the
center-eliminated certificate value. This keeps the strictness needed at the
optimal configuration, where equality in a weak bound is possible.
-/

set_option maxHeartbeats 600000

namespace ThreeSquares
namespace CenterElimination

open scoped NNReal
open SquarePacking

noncomputable section

/-- Extract the rational inequalities checked by a well-formed certificate. -/
theorem Certificate.wellFormed_data (C : Certificate) (hC : C.wellFormed = true) :
    (∀ i : Fin 3, (((∀ k : Fin 4, 0 ≤ C.lam i k) ∧ 0 ≤ C.mu i) ∧
      0 ≤ C.invWeight i) ∧ C.invWeight i * C.weight i = 1) ∧
      C.weight 0 + C.weight 1 + C.weight 2 = 1 := by
  simpa [Certificate.wellFormed, List.all_eq_true] using hC

private theorem Certificate.weight_pos (C : Certificate) (hC : C.wellFormed = true)
    (i : Fin 3) : 0 < C.weight i := by
  have hd := C.wellFormed_data hC
  have hi := hd.1 i
  have hiw : (0 : ℚ) ≤ C.invWeight i := hi.1.2
  have hprod : C.invWeight i * C.weight i = 1 := hi.2
  by_contra hn
  have hw : C.weight i ≤ 0 := le_of_not_gt hn
  have hnonpos : C.invWeight i * C.weight i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hiw hw
  linarith

private theorem force_identity (C : Certificate) (x : Fin 4 → ℝ) (c : Fin 3 → Plane) :
    ∑ i, (c i 0 * (C.forceE i axisU).eval x + c i 1 * (C.forceE i axisV).eval x) =
      ∑ e, (C.signedMu e : ℝ) *
        ((axisU e (C.axis e)).eval x * (c (pairSnd e) 0 - c (pairFst e) 0) +
          (axisV e (C.axis e)).eval x * (c (pairSnd e) 1 - c (pairFst e) 1)) := by
  simp only [Certificate.forceE, sum3_eval, IntervalExpr.eval, Fin.sum_univ_three,
    Certificate.coef, pairFst, pairSnd]
  simp
  ring

private theorem exists_pos_of_sum_pos (f : Fin 4 → ℝ) (h : 0 < ∑ k, f k) :
    ∃ k, 0 < f k := by
  by_contra hn
  push Not at hn
  have hle : ∑ k, f k ≤ 0 := by
    apply Finset.sum_nonpos
    intro k _
    exact hn k
  linarith

/-- The total weighted mean of the vertex squared norms. -/
def weightedVertexMean (C : Certificate) (x : Fin 4 → ℝ) (c : Fin 3 → Plane) : ℝ :=
  ∑ i, ∑ k, (C.lam i k : ℝ) *
    ((c i 0 + (cosR x i * cornerX k + -sinR x i * cornerY k)) ^ 2 +
      (c i 1 + (sinR x i * cornerX k + cosR x i * cornerY k)) ^ 2)

/-- The center-free lower bound is at most the weighted mean of the twelve
vertex squared norms. No radius bound is assumed in this algebraic lemma. -/
theorem Certificate.lowerBoundRaw_le_weightedVertexMean (C : Certificate)
    (hC : C.wellFormed = true) (x : Fin 4 → ℝ)
    (hu1 : x 0 ^ 2 + x 1 ^ 2 = 1) (hu2 : x 2 ^ 2 + x 3 ^ 2 = 1)
    (c : Fin 3 → Plane) (hs : ∀ e, BranchSeparation C x c e) :
    C.lowerBoundRaw.eval x ≤ weightedVertexMean C x c := by
  have hdata := C.wellFormed_data hC
  have hunit (i : Fin 3) : cosR x i ^ 2 + sinR x i ^ 2 = 1 := by
    fin_cases i <;> simp [cosR, sinR, cosE, sinE, IntervalExpr.eval, hu1, hu2]
  have hsq (i : Fin 3) :=
    square_completion (c i 0) (c i 1) (cosR x i) (sinR x i)
      ((C.forceE i axisU).eval x) ((C.forceE i axisV).eval x) (C.invWeight i)
      (fun k => (C.lam i k : ℝ)) (hunit i)
      (by
        have hi := (hdata.1 i).2
        simp only [Certificate.weight] at hi
        exact_mod_cast hi)
      (by exact_mod_cast (hdata.1 i).1.2)
  have hsep : ∑ e, (C.mu e : ℝ) * (halfWidthE e (C.axis e)).eval x ≤
      ∑ e, (C.signedMu e : ℝ) *
        ((axisU e (C.axis e)).eval x * (c (pairSnd e) 0 - c (pairFst e) 0) +
          (axisV e (C.axis e)).eval x * (c (pairSnd e) 1 - c (pairFst e) 1)) := by
    apply Finset.sum_le_sum
    intro e _
    have h := hs e
    have hmu : (0 : ℝ) ≤ C.mu e := by exact_mod_cast (hdata.1 e).1.1.2
    simp only [BranchSeparation] at h
    unfold Certificate.signedMu
    split_ifs at h ⊢ with hsg
    · exact mul_le_mul_of_nonneg_left h hmu
    · push_cast
      nlinarith [mul_le_mul_of_nonneg_left h hmu]
  have hforce := force_identity C x c
  have hsum : ((C.weight 0 + C.weight 1 + C.weight 2 : ℚ) : ℝ) = 1 := by
    exact_mod_cast hdata.2
  have hsumR : (C.weight 0 : ℝ) + C.weight 1 + C.weight 2 = 1 := by
    exact_mod_cast hdata.2
  have hsum_lam := hsum
  simp only [Certificate.weight] at hsum_lam
  push_cast at hsum_lam
  have h0 := hsq 0
  have h1 := hsq 1
  have h2 := hsq 2
  simp only [Certificate.lowerBoundRaw, sub_eval, sum3_eval, IntervalExpr.eval,
    Certificate.residualX, Certificate.residualY, Certificate.zetaX, Certificate.zetaY]
  push_cast
  simp only [Fin.sum_univ_three] at hsep hforce ⊢
  simp only [cosR, sinR] at h0 h1 h2
  simp only [weightedVertexMean, Fin.sum_univ_four]
  have hrows :
      (∑ i, ((∑ k, (C.lam i k : ℝ)) / 2 -
        (C.invWeight i : ℝ) *
          (((cosR x i * (∑ k, (C.lam i k : ℝ) * cornerX k) -
                sinR x i * (∑ k, (C.lam i k : ℝ) * cornerY k)) -
              1 / 2 * (C.forceE i axisU).eval x) ^ 2 +
            ((sinR x i * (∑ k, (C.lam i k : ℝ) * cornerX k) +
                cosR x i * (∑ k, (C.lam i k : ℝ) * cornerY k)) -
              1 / 2 * (C.forceE i axisV).eval x) ^ 2))) ≤
      ∑ i, ((∑ k, (C.lam i k : ℝ) *
          ((c i 0 + (cosR x i * cornerX k + -sinR x i * cornerY k)) ^ 2 +
            (c i 1 + (sinR x i * cornerX k + cosR x i * cornerY k)) ^ 2)) -
        (c i 0 * (C.forceE i axisU).eval x + c i 1 * (C.forceE i axisV).eval x)) := by
    simp only [Fin.sum_univ_three, Fin.sum_univ_four] at h0 h1 h2 ⊢
    simp only [cosR, sinR] at ⊢
    linarith [h0, h1, h2]
  simp only [cosR, sinR] at hrows
  simp only [Fin.sum_univ_three] at hrows hsep hforce ⊢
  simp only [Fin.sum_univ_four] at hrows
  simp only [cosR, sinR] at ⊢
  linarith [hrows, hsep, hforce, hsum_lam]

/-- Strict subcritical vertex inequalities make the weighted vertex mean
strictly less than the candidate squared radius. -/
theorem Certificate.weightedVertexMean_lt (C : Certificate)
  (hC : C.wellFormed = true) (P : SubcriticalRationalRotationPacking 3)
    (h0 : P.t 0 = 0) :
    weightedVertexMean C (rotationVector (P.t 1) (P.t 2)) P.centers < 425 / 256 := by
  have hd := C.wellFormed_data hC
  have hrow_sum (i : Fin 3) :
      (∑ k, (C.lam i k : ℝ)) = (C.weight i : ℝ) := by
    have hq : (∑ k, C.lam i k) = C.weight i := by
      simp [Certificate.weight, Fin.sum_univ_four, add_assoc]
    exact_mod_cast hq
  have hrow_weight_pos (i : Fin 3) : 0 < (C.weight i : ℝ) := by
    exact_mod_cast C.weight_pos hC i
  have hrow_lambda_pos (i : Fin 3) : ∃ k : Fin 4, 0 < (C.lam i k : ℝ) := by
    apply exists_pos_of_sum_pos (fun k => (C.lam i k : ℝ))
    rw [hrow_sum i]
    exact hrow_weight_pos i
  have hvertex (i : Fin 3) (k : Fin 4) :
      (P.centers i 0 + (rationalCos (P.t i) * cornerX k +
          -rationalSin (P.t i) * cornerY k)) ^ 2 +
       (P.centers i 1 + (rationalSin (P.t i) * cornerX k +
          rationalCos (P.t i) * cornerY k)) ^ 2 < 425 / 256 := by
    have hv := P.vertices i
    unfold StrictCandidateVertexInequalities at hv
    simp only [vertexSquared_rational] at hv
    fin_cases k
    · simpa [cornerX, cornerY] using hv.1
    · simpa [cornerX, cornerY] using hv.2.1
    · simpa [cornerX, cornerY] using hv.2.2.1
    · simpa [cornerX, cornerY] using hv.2.2.2
  have hrow_lt (i : Fin 3) :
      (∑ k, (C.lam i k : ℝ) *
        ((P.centers i 0 + (rationalCos (P.t i) * cornerX k +
            -rationalSin (P.t i) * cornerY k)) ^ 2 +
         (P.centers i 1 + (rationalSin (P.t i) * cornerX k +
            rationalCos (P.t i) * cornerY k)) ^ 2)) <
        (C.weight i : ℝ) * (425 / 256) := by
    calc
      (∑ k, (C.lam i k : ℝ) *
        ((P.centers i 0 + (rationalCos (P.t i) * cornerX k +
            -rationalSin (P.t i) * cornerY k)) ^ 2 +
         (P.centers i 1 + (rationalSin (P.t i) * cornerX k +
            rationalCos (P.t i) * cornerY k)) ^ 2)) =
          ∑ k ∈ (Finset.univ : Finset (Fin 4)), (C.lam i k : ℝ) *
            ((P.centers i 0 + (rationalCos (P.t i) * cornerX k +
                -rationalSin (P.t i) * cornerY k)) ^ 2 +
             (P.centers i 1 + (rationalSin (P.t i) * cornerX k +
                rationalCos (P.t i) * cornerY k)) ^ 2) := by simp
      _ < ∑ k : Fin 4,
            (C.lam i k : ℝ) * (425 / 256) := by
              apply Finset.sum_lt_sum
              · intro k _
                exact mul_le_mul_of_nonneg_left (le_of_lt (hvertex i k))
                  (by exact_mod_cast (hd.1 i).1.1.1 k)
              · obtain ⟨k, hk⟩ := hrow_lambda_pos i
                exact ⟨k, Finset.mem_univ _, mul_lt_mul_of_pos_left (hvertex i k) hk⟩
      _ = (C.weight i : ℝ) * (425 / 256) := by
            rw [← Finset.sum_mul]
            exact congrArg (fun z : ℝ => z * (425 / 256)) (hrow_sum i)
  have hsum : ((C.weight 0 + C.weight 1 + C.weight 2 : ℚ) : ℝ) = 1 := by
    exact_mod_cast hd.2
  have hsumR : (C.weight 0 : ℝ) + C.weight 1 + C.weight 2 = 1 := by
    exact_mod_cast hd.2
  let x := rotationVector (P.t 1) (P.t 2)
  have hcos (i : Fin 3) : cosR (rotationVector (P.t 1) (P.t 2)) i = rationalCos (P.t i) := by
    fin_cases i <;> simp [cosR, cosE, IntervalExpr.eval, rotationVector, rationalCos, h0]
  have hsin (i : Fin 3) : sinR (rotationVector (P.t 1) (P.t 2)) i = rationalSin (P.t i) := by
    fin_cases i <;> simp [sinR, sinE, IntervalExpr.eval, rotationVector, rationalSin, h0]
  have hmean_eq : weightedVertexMean C (rotationVector (P.t 1) (P.t 2)) P.centers =
      ∑ i, ∑ k, (C.lam i k : ℝ) *
        ((P.centers i 0 + (rationalCos (P.t i) * cornerX k +
            -rationalSin (P.t i) * cornerY k)) ^ 2 +
         (P.centers i 1 + (rationalSin (P.t i) * cornerX k +
            rationalCos (P.t i) * cornerY k)) ^ 2) := by
    simp only [weightedVertexMean, hcos, hsin]
  calc
    weightedVertexMean C (rotationVector (P.t 1) (P.t 2)) P.centers =
      ∑ i, (∑ k, (C.lam i k : ℝ) *
        ((P.centers i 0 + (rationalCos (P.t i) * cornerX k +
            -rationalSin (P.t i) * cornerY k)) ^ 2 +
         (P.centers i 1 + (rationalSin (P.t i) * cornerX k +
            rationalCos (P.t i) * cornerY k)) ^ 2)) := hmean_eq
    _ < ∑ i, (C.weight i : ℝ) * (425 / 256) := by
      calc
        _ = ∑ i ∈ (Finset.univ : Finset (Fin 3)),
            ∑ k, (C.lam i k : ℝ) *
              ((P.centers i 0 + (rationalCos (P.t i) * cornerX k +
                  -rationalSin (P.t i) * cornerY k)) ^ 2 +
               (P.centers i 1 + (rationalSin (P.t i) * cornerX k +
                  rationalCos (P.t i) * cornerY k)) ^ 2) := by simp
        _ < ∑ i ∈ (Finset.univ : Finset (Fin 3)),
            (C.weight i : ℝ) * (425 / 256) :=
              Finset.sum_lt_sum (fun i _ => (hrow_lt i).le)
                ⟨0, Finset.mem_univ _, hrow_lt 0⟩
        _ = ∑ i, (C.weight i : ℝ) * (425 / 256) := by simp
    _ = 425 / 256 := by
      simp only [Fin.sum_univ_three]
      calc
        (C.weight 0 : ℝ) * (425 / 256) + (C.weight 1 : ℝ) * (425 / 256) +
            (C.weight 2 : ℝ) * (425 / 256) =
            ((C.weight 0 : ℝ) + C.weight 1 + C.weight 2) * (425 / 256) := by ring
      _ = 1 * (425 / 256) := by rw [hsumR]
        _ = 425 / 256 := by ring

/-- A well-formed certificate's lower bound is strictly below the candidate
for every subcritical packing realizing its signed separation branch. -/
theorem Certificate.lowerBound_lt_of_realizes (C : Certificate)
    (hC : C.wellFormed = true) (P : SubcriticalRationalRotationPacking 3)
    (h0 : P.t 0 = 0) (hreal : Realizes P C.code) :
    C.lowerBound.eval (rotationVector (P.t 1) (P.t 2)) < 425 / 256 := by
  set x := rotationVector (P.t 1) (P.t 2)
  have hmean := Certificate.weightedVertexMean_lt C hC P h0
  have hunit (i : Fin 3) : cosR x i ^ 2 + sinR x i ^ 2 = 1 := by
    fin_cases i <;> simp [x, cosR, sinR, cosE, sinE, IntervalExpr.eval,
      rotationVector, rational_rotation_unit]
  have hreal' (e : Fin 3) : BranchSeparation C x P.centers e := by
    exact hreal e
  have hle := C.lowerBoundRaw_le_weightedVertexMean hC x
    (by simpa [x, rotationVector] using rational_rotation_unit (P.t 1))
    (by simpa [x, rotationVector] using rational_rotation_unit (P.t 2))
    P.centers hreal'
  rw [lowerBound_eval C x (hunit 1) (hunit 2)]
  exact lt_of_le_of_lt hle hmean

#print axioms Certificate.lowerBound_lt_of_realizes

end

end CenterElimination
end ThreeSquares
