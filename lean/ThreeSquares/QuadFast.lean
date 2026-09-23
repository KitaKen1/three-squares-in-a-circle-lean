import ThreeSquares.QuadCertificate

/-! # Fast kernel evaluation of the second-order check

The quadratic bound is evaluated exactly at fifteen rational points; finite
differences recover its gradient and Hessian.  The resulting Boolean check is
proved equal to `Certificate.qcheck`, so all soundness theorems transfer.
-/

namespace ThreeSquares
namespace CenterElimination

open scoped NNReal
open SquarePacking

noncomputable section

/- ## Fast evaluation: finite differences of exact point values

The kernel evaluates the quadratic bound only at fifteen rational points;
finite differences recover the gradient and the Hessian exactly. -/

def evalQ {n : ℕ} (p : Fin n → ℚ) : IntervalExpr n → ℚ
  | .const q => q
  | .var i => p i
  | .add e f => evalQ p e + evalQ p f
  | .neg e => -evalQ p e
  | .mul e f => evalQ p e * evalQ p f
  | .square e => evalQ p e ^ 2
  | .abs e => |evalQ p e|

theorem evalQ_cast {n : ℕ} (e : IntervalExpr n) (p : Fin n → ℚ) :
    ((evalQ p e : ℚ) : ℝ) = e.eval (fun i => (p i : ℝ)) := by
  induction e <;> simp [evalQ, IntervalExpr.eval, *]

def cosDE (o q : Fin 3) : E := .add (.mul (cosE o) (cosE q)) (.mul (sinE o) (sinE q))
def sinDE (o q : Fin 3) : E := sub (.mul (sinE q) (cosE o)) (.mul (cosE q) (sinE o))

def halfWidthQE (σ : ℚ) (e : Fin 3) (a : Fin 4) : E :=
  .mul (.const (1 / 2)) (.add (.const 1) (.add (cosDE (axisOwner e a) (axisOther e a))
    (.mul (.const σ) (sinDE (axisOwner e a) (axisOther e a)))))

def Certificate.lowerQE (C : Certificate) (σ : Fin 3 → ℚ) : E :=
  sub (.add (.const (1 / 2)) (sum3 fun e => .mul (.const (C.mu e)) (halfWidthQE (σ e) e (C.axis e))))
    (sum3 fun i => .mul (.const (C.invWeight i))
      (.add (.square (C.residualXg i)) (.square (C.residualYg i))))

theorem lowerQE_eval (C : Certificate) (σ : Fin 3 → ℚ) (x : Fin 4 → ℝ) :
    (C.lowerQE σ).eval x = (C.lowerQuad σ).eval x := by
  have hr (i : Fin 3) := residualA_eval C x i
  simp only [Certificate.lowerQE, Certificate.lowerQuad, sub_eval, sum3_eval, sum3Q_eval,
    IntervalExpr.eval, Quad.eval_add, Quad.eval_smul, Quad.eval_toQuad, Aff.eval_const,
    Quad.eval_mul, halfWidthQE, halfWidthQ, cosDE, sinDE, cosDiff, sinDiff, cosA_eval, sinA_eval,
    (hr _).1, (hr _).2, Fin.sum_univ_three]
  simp only [cosR, sinR]
  push_cast
  ring

theorem Quad.value_cast (q : Quad) (p : Fin 4 → ℚ) :
    ((q.value p : ℚ) : ℝ) = q.eval (fun i => (p i : ℝ)) := by
  simp [Quad.value, Quad.eval]

def shiftPt (p : Fin 4 → ℚ) (i : Fin 4) (s : ℚ) : Fin 4 → ℚ :=
  fun k => if k = i then p k + s else p k

structure FD where
  f0 : ℚ
  g : Fin 4 → ℚ
  d : Fin 4 → ℚ
  s : Fin 4 → Fin 4 → ℚ

def fdData (f : (Fin 4 → ℚ) → ℚ) (m : Fin 4 → ℚ) : FD where
  f0 := f m
  g i := (f (shiftPt m i 1) - f (shiftPt m i (-1))) / 2
  d i := f (shiftPt m i 1) + f (shiftPt m i (-1)) - 2 * f m
  s i j := f (shiftPt (shiftPt m i 1) j 1) - f (shiftPt m i 1) - f (shiftPt m j 1) + f m

def fdLower (D : FD) (lin m h : Fin 4 → ℚ) : ℚ :=
  (D.f0 + ∑ i, lin i * m i) - ∑ i, |D.g i + lin i| * h i +
    ∑ i, min 0 (D.d i / 2) * h i ^ 2 -
    ∑ i, ∑ j, (if i < j then |D.s i j| * h i * h j else 0)

theorem fd_g (q : Quad) (m : Fin 4 → ℚ) (i : Fin 4) :
    (q.value (shiftPt m i 1) - q.value (shiftPt m i (-1))) / 2 = q.grad m i := by
  fin_cases i <;> simp [Quad.value, Quad.grad, shiftPt, Fin.sum_univ_four] <;> ring

theorem fd_d (q : Quad) (m : Fin 4 → ℚ) (i : Fin 4) :
    q.value (shiftPt m i 1) + q.value (shiftPt m i (-1)) - 2 * q.value m = 2 * q.m i i := by
  fin_cases i <;> simp [Quad.value, shiftPt, Fin.sum_univ_four] <;> ring

theorem fd_s (q : Quad) (m : Fin 4 → ℚ) (i j : Fin 4) (hij : i < j) :
    q.value (shiftPt (shiftPt m i 1) j 1) - q.value (shiftPt m i 1) - q.value (shiftPt m j 1) +
      q.value m = q.m i j + q.m j i := by
  fin_cases i <;> fin_cases j <;> simp_all [Quad.value, shiftPt, Fin.sum_univ_four] <;> ring

/-- Linear shift coefficients from a gradient. -/
def shiftLin (region : ℤ) (g : Fin 4 → ℚ) : Fin 4 → ℚ :=
  if region < 0 then ![-(max 0 (g 0)), max 0 (-(g 1)), max 0 (g 0), -(max 0 (-(g 1)))]
  else if 0 < region then ![max 0 (g 2), -(max 0 (-(g 3))), -(max 0 (g 2)), max 0 (-(g 3))]
  else fun _ => 0

theorem lower_add_shift (q : Quad) (region : ℤ) (B : RationalBox 4) :
    (Quad.add q (Certificate.shift region q (Quad.midpoint B))).lower B =
      fdLower ⟨q.value (Quad.midpoint B), q.grad (Quad.midpoint B), fun i => 2 * q.m i i,
        fun i j => q.m i j + q.m j i⟩
        (shiftLin region (q.grad (Quad.midpoint B))) (Quad.midpoint B) (Quad.radius B) := by
  unfold Certificate.shift shiftLin
  split_ifs <;>
    simp only [Quad.lower, fdLower, Quad.value, Quad.grad, Quad.add, Quad.smul, Aff.toQuad,
      Aff.add, Aff.var, Aff.neg, Aff.smul, Fin.sum_univ_four] <;>
    simp <;> ring_nf

def Certificate.qcheckFast (C : Certificate) (B : RationalBox 4) (region : ℤ) : Bool :=
  let mid := Quad.midpoint B
  let D := fdData (fun p => evalQ p (C.lowerQE (fun e => widthSign region mid e (C.axis e)))) mid
  C.wellFormed && decide (425 / 256 < fdLower D (shiftLin region D.g) mid (Quad.radius B))


theorem fdLower_quad (q : Quad) (lin m h : Fin 4 → ℚ) :
    fdLower (fdData q.value m) lin m h =
      fdLower ⟨q.value m, q.grad m, fun i => 2 * q.m i i, fun i j => q.m i j + q.m j i⟩
        lin m h := by
  have hg (i : Fin 4) := fd_g q m i
  have hd (i : Fin 4) := fd_d q m i
  simp only [fdLower, fdData, Fin.sum_univ_four, hg, hd]
  rw [fd_s q m 0 1 (by decide), fd_s q m 0 2 (by decide), fd_s q m 0 3 (by decide),
    fd_s q m 1 2 (by decide), fd_s q m 1 3 (by decide), fd_s q m 2 3 (by decide)]
  simp only [show ¬ ((0 : Fin 4) < 0) by decide, show (0 : Fin 4) < 1 by decide,
    show (0 : Fin 4) < 2 by decide, show (0 : Fin 4) < 3 by decide,
    show ¬ ((1 : Fin 4) < 0) by decide, show ¬ ((1 : Fin 4) < 1) by decide,
    show (1 : Fin 4) < 2 by decide, show (1 : Fin 4) < 3 by decide,
    show ¬ ((2 : Fin 4) < 0) by decide, show ¬ ((2 : Fin 4) < 1) by decide,
    show ¬ ((2 : Fin 4) < 2) by decide, show (2 : Fin 4) < 3 by decide,
    show ¬ ((3 : Fin 4) < 0) by decide, show ¬ ((3 : Fin 4) < 1) by decide,
    show ¬ ((3 : Fin 4) < 2) by decide, show ¬ ((3 : Fin 4) < 3) by decide,
    if_true, if_false]

theorem fdData_g (q : Quad) (m : Fin 4 → ℚ) : (fdData q.value m).g = q.grad m := by
  funext i; exact fd_g q m i

theorem qcheckFast_eq (C : Certificate) (B : RationalBox 4) (region : ℤ) :
    C.qcheckFast B region = C.qcheck B region := by
  unfold Certificate.qcheckFast Certificate.qcheck
  set σ : Fin 3 → ℚ := fun e => widthSign region (Quad.midpoint B) e (C.axis e)
  have hf : (fun p => evalQ p (C.lowerQE σ)) = (C.lowerQuad σ).value := by
    funext p
    have h1 := evalQ_cast (C.lowerQE σ) p
    rw [lowerQE_eval, ← Quad.value_cast] at h1
    exact_mod_cast h1
  simp only []
  rw [hf, fdData_g, fdLower_quad, lower_add_shift]

end

end CenterElimination
end ThreeSquares
