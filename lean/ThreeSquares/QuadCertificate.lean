import ThreeSquares.CenterElimination

/-! # Second-order checks for center-eliminating certificates

Every term of the center-eliminated bound is a polynomial of degree at most two
in `x = (cos₁, sin₁, cos₂, sin₂)`, except the absolute values of projected
widths.  Each width is `|cos Δ| + |sin Δ|` for a relative angle `Δ`, which is
at least `cos Δ + σ sin Δ` for every `σ ∈ {-1, 0, 1}`.  With these choices the
bound becomes a quadratic polynomial.  Its value on a box is enclosed by a
Taylor form around the midpoint, whose error is quadratic in the box width.

Near the diagonal the sign of `sin (θ₁ - θ₂)` is fixed only on one side of
`t₁ = t₂`; a region hypothesis `t₁ ≤ t₂` or `t₂ ≤ t₁` then also allows adding
a nonpositive multiple of `sin₁ - sin₂`.  All choices affect only tightness,
never soundness.
-/

namespace ThreeSquares
namespace CenterElimination

open scoped NNReal
open SquarePacking

noncomputable section

/- ## Affine and quadratic forms in four variables -/

structure Aff where
  c : ℚ
  v : Fin 4 → ℚ

structure Quad where
  c : ℚ
  v : Fin 4 → ℚ
  m : Fin 4 → Fin 4 → ℚ

namespace Aff

def eval (a : Aff) (x : Fin 4 → ℝ) : ℝ := a.c + ∑ i, (a.v i : ℝ) * x i

def const (q : ℚ) : Aff := ⟨q, fun _ => 0⟩
def var (k : Fin 4) : Aff := ⟨0, fun i => if i = k then 1 else 0⟩
def add (a b : Aff) : Aff := ⟨a.c + b.c, fun i => a.v i + b.v i⟩
def smul (q : ℚ) (a : Aff) : Aff := ⟨q * a.c, fun i => q * a.v i⟩
def neg (a : Aff) : Aff := smul (-1) a

/-- Product of two affine forms. -/
def mul (a b : Aff) : Quad :=
  ⟨a.c * b.c, fun i => a.c * b.v i + b.c * a.v i, fun i j => a.v i * b.v j⟩

def toQuad (a : Aff) : Quad := ⟨a.c, a.v, fun _ _ => 0⟩

@[simp] theorem eval_const (q : ℚ) (x : Fin 4 → ℝ) : (const q).eval x = q := by
  simp [eval, const]

@[simp] theorem eval_var (k : Fin 4) (x : Fin 4 → ℝ) : (var k).eval x = x k := by
  fin_cases k <;> simp [eval, var, Fin.sum_univ_four]

@[simp] theorem eval_add (a b : Aff) (x : Fin 4 → ℝ) :
    (add a b).eval x = a.eval x + b.eval x := by
  simp only [eval, add, Fin.sum_univ_four]; push_cast; ring

@[simp] theorem eval_smul (q : ℚ) (a : Aff) (x : Fin 4 → ℝ) :
    (smul q a).eval x = q * a.eval x := by
  simp only [eval, smul, Fin.sum_univ_four]; push_cast; ring

@[simp] theorem eval_neg (a : Aff) (x : Fin 4 → ℝ) : (neg a).eval x = -a.eval x := by
  simp [neg]

end Aff

namespace Quad

def eval (q : Quad) (x : Fin 4 → ℝ) : ℝ :=
  q.c + ∑ i, (q.v i : ℝ) * x i + ∑ i, ∑ j, (q.m i j : ℝ) * x i * x j

def add (p q : Quad) : Quad := ⟨p.c + q.c, fun i => p.v i + q.v i, fun i j => p.m i j + q.m i j⟩
def smul (r : ℚ) (q : Quad) : Quad := ⟨r * q.c, fun i => r * q.v i, fun i j => r * q.m i j⟩

@[simp] theorem eval_add (p q : Quad) (x : Fin 4 → ℝ) :
    (add p q).eval x = p.eval x + q.eval x := by
  simp only [eval, add, Fin.sum_univ_four]; push_cast; ring

@[simp] theorem eval_smul (r : ℚ) (q : Quad) (x : Fin 4 → ℝ) :
    (smul r q).eval x = r * q.eval x := by
  simp only [eval, smul, Fin.sum_univ_four]; push_cast; ring

@[simp] theorem eval_mul (a b : Aff) (x : Fin 4 → ℝ) :
    (Aff.mul a b).eval x = a.eval x * b.eval x := by
  simp only [eval, Aff.eval, Aff.mul, Fin.sum_univ_four]; push_cast; ring

@[simp] theorem eval_toQuad (a : Aff) (x : Fin 4 → ℝ) : a.toQuad.eval x = a.eval x := by
  simp [eval, Aff.eval, Aff.toQuad]

def midpoint (B : RationalBox 4) (i : Fin 4) : ℚ := ((B i).lo + (B i).hi) / 2
def radius (B : RationalBox 4) (i : Fin 4) : ℚ := ((B i).hi - (B i).lo) / 2

/-- Gradient at a rational point. -/
def grad (q : Quad) (p : Fin 4 → ℚ) (i : Fin 4) : ℚ := q.v i + ∑ j, (q.m i j + q.m j i) * p j

def value (q : Quad) (p : Fin 4 → ℚ) : ℚ :=
  q.c + ∑ i, q.v i * p i + ∑ i, ∑ j, q.m i j * p i * p j

/-- Taylor lower bound around the midpoint of the box. -/
def lower (q : Quad) (B : RationalBox 4) : ℚ :=
  q.value (midpoint B) - ∑ i, |q.grad (midpoint B) i| * radius B i +
    ∑ i, min 0 (q.m i i) * radius B i ^ 2 -
    ∑ i, ∑ j, (if i < j then |q.m i j + q.m j i| * radius B i * radius B j else 0)

private theorem lin_bound {g ξ h : ℝ} (hξ : |ξ| ≤ h) : -(|g| * h) ≤ g * ξ := by
  have := abs_mul g ξ
  have h1 : |g * ξ| ≤ |g| * h := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hξ (abs_nonneg g)
  linarith [neg_abs_le (g * ξ)]

private theorem diag_bound {m ξ h : ℝ} (hξ : |ξ| ≤ h) : min 0 m * h ^ 2 ≤ m * ξ ^ 2 := by
  have hsq : ξ ^ 2 ≤ h ^ 2 := by
    have := sq_abs ξ
    nlinarith [abs_nonneg ξ]
  rcases le_total 0 m with hm | hm
  · rw [min_eq_left hm]; simp; positivity
  · rw [min_eq_right hm]; nlinarith [sq_nonneg ξ]

private theorem off_bound {m ξ η h k : ℝ} (hξ : |ξ| ≤ h) (hη : |η| ≤ k) :
    -(|m| * h * k) ≤ m * ξ * η := by
  have h1 : |m * ξ * η| ≤ |m| * h * k := by
    rw [abs_mul, abs_mul]
    have hh : 0 ≤ h := (abs_nonneg ξ).trans hξ
    exact mul_le_mul (mul_le_mul_of_nonneg_left hξ (abs_nonneg m)) hη (abs_nonneg η)
      (mul_nonneg (abs_nonneg m) hh)
  linarith [neg_abs_le (m * ξ * η)]

theorem lower_le (q : Quad) {B : RationalBox 4} {x : Fin 4 → ℝ} (hx : B.Contains x) :
    (q.lower B : ℝ) ≤ q.eval x := by
  set mid := midpoint B
  set h := radius B
  have hξ (i : Fin 4) : |x i - mid i| ≤ h i := by
    have := hx i
    simp only [RationalInterval.Contains] at this
    simp only [mid, h, midpoint, radius]
    push_cast
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  set g := q.grad mid
  set ξ : Fin 4 → ℝ := fun i => x i - mid i with hξdef
  have hid : q.eval x = (q.value mid : ℝ) +
      ((g 0 : ℝ) * ξ 0 + (g 1 : ℝ) * ξ 1 + (g 2 : ℝ) * ξ 2 + (g 3 : ℝ) * ξ 3) +
      ((q.m 0 0 : ℝ) * ξ 0 ^ 2 + (q.m 1 1 : ℝ) * ξ 1 ^ 2 + (q.m 2 2 : ℝ) * ξ 2 ^ 2 +
        (q.m 3 3 : ℝ) * ξ 3 ^ 2) +
      (((q.m 0 1 : ℝ) + q.m 1 0) * ξ 0 * ξ 1 + ((q.m 0 2 : ℝ) + q.m 2 0) * ξ 0 * ξ 2 +
        ((q.m 0 3 : ℝ) + q.m 3 0) * ξ 0 * ξ 3 + ((q.m 1 2 : ℝ) + q.m 2 1) * ξ 1 * ξ 2 +
        ((q.m 1 3 : ℝ) + q.m 3 1) * ξ 1 * ξ 3 + ((q.m 2 3 : ℝ) + q.m 3 2) * ξ 2 * ξ 3) := by
    simp only [eval, value, g, grad, ξ, Fin.sum_univ_four]; push_cast; ring
  have hlow : (q.lower B : ℝ) = (q.value mid : ℝ) -
      (|(g 0 : ℝ)| * h 0 + |(g 1 : ℝ)| * h 1 + |(g 2 : ℝ)| * h 2 + |(g 3 : ℝ)| * h 3) +
      (min 0 (q.m 0 0 : ℝ) * (h 0 : ℝ) ^ 2 + min 0 (q.m 1 1 : ℝ) * (h 1 : ℝ) ^ 2 +
        min 0 (q.m 2 2 : ℝ) * (h 2 : ℝ) ^ 2 + min 0 (q.m 3 3 : ℝ) * (h 3 : ℝ) ^ 2) -
      (|(q.m 0 1 : ℝ) + q.m 1 0| * h 0 * h 1 + |(q.m 0 2 : ℝ) + q.m 2 0| * h 0 * h 2 +
        |(q.m 0 3 : ℝ) + q.m 3 0| * h 0 * h 3 + |(q.m 1 2 : ℝ) + q.m 2 1| * h 1 * h 2 +
        |(q.m 1 3 : ℝ) + q.m 3 1| * h 1 * h 3 + |(q.m 2 3 : ℝ) + q.m 3 2| * h 2 * h 3) := by
    simp only [lower, g, Fin.sum_univ_four]
    simp only [show ¬ ((0 : Fin 4) < 0) by decide, show (0 : Fin 4) < 1 by decide,
      show (0 : Fin 4) < 2 by decide, show (0 : Fin 4) < 3 by decide,
      show ¬ ((1 : Fin 4) < 0) by decide, show ¬ ((1 : Fin 4) < 1) by decide,
      show (1 : Fin 4) < 2 by decide, show (1 : Fin 4) < 3 by decide,
      show ¬ ((2 : Fin 4) < 0) by decide, show ¬ ((2 : Fin 4) < 1) by decide,
      show ¬ ((2 : Fin 4) < 2) by decide, show (2 : Fin 4) < 3 by decide,
      show ¬ ((3 : Fin 4) < 0) by decide, show ¬ ((3 : Fin 4) < 1) by decide,
      show ¬ ((3 : Fin 4) < 2) by decide, show ¬ ((3 : Fin 4) < 3) by decide,
      if_true, if_false]
    push_cast; ring
  rw [hid, hlow]
  have l0 := lin_bound (g := (g 0 : ℝ)) (hξ 0)
  have l1 := lin_bound (g := (g 1 : ℝ)) (hξ 1)
  have l2 := lin_bound (g := (g 2 : ℝ)) (hξ 2)
  have l3 := lin_bound (g := (g 3 : ℝ)) (hξ 3)
  have d0 := diag_bound (m := (q.m 0 0 : ℝ)) (hξ 0)
  have d1 := diag_bound (m := (q.m 1 1 : ℝ)) (hξ 1)
  have d2 := diag_bound (m := (q.m 2 2 : ℝ)) (hξ 2)
  have d3 := diag_bound (m := (q.m 3 3 : ℝ)) (hξ 3)
  have o01 := off_bound (m := (q.m 0 1 : ℝ) + q.m 1 0) (hξ 0) (hξ 1)
  have o02 := off_bound (m := (q.m 0 2 : ℝ) + q.m 2 0) (hξ 0) (hξ 2)
  have o03 := off_bound (m := (q.m 0 3 : ℝ) + q.m 3 0) (hξ 0) (hξ 3)
  have o12 := off_bound (m := (q.m 1 2 : ℝ) + q.m 2 1) (hξ 1) (hξ 2)
  have o13 := off_bound (m := (q.m 1 3 : ℝ) + q.m 3 1) (hξ 1) (hξ 3)
  have o23 := off_bound (m := (q.m 2 3 : ℝ) + q.m 3 2) (hξ 2) (hξ 3)
  simp only [ξ] at l0 l1 l2 l3 d0 d1 d2 d3 o01 o02 o03 o12 o13 o23 ⊢
  linarith

end Quad

/- ## The quadratic lower bound of a certificate -/

def cosA : Fin 3 → Aff := ![Aff.const 1, Aff.var 0, Aff.var 2]
def sinA : Fin 3 → Aff := ![Aff.const 0, Aff.var 1, Aff.var 3]
def slotXA (s : Fin 3) : Fin 2 → Aff := ![cosA s, (sinA s).neg]
def slotYA (s : Fin 3) : Fin 2 → Aff := ![sinA s, cosA s]

theorem cosA_eval (x : Fin 4 → ℝ) (i : Fin 3) : (cosA i).eval x = cosR x i := by
  fin_cases i <;> simp [cosA, cosR, cosE, IntervalExpr.eval]

theorem sinA_eval (x : Fin 4 → ℝ) (i : Fin 3) : (sinA i).eval x = sinR x i := by
  fin_cases i <;> simp [sinA, sinR, sinE, IntervalExpr.eval]

theorem slotA_eval (x : Fin 4 → ℝ) (s : Fin 3) (col : Fin 2) :
    (slotXA s col).eval x = (slotX s col).eval x ∧
      (slotYA s col).eval x = (slotY s col).eval x := by
  fin_cases col <;>
    simp [slotXA, slotYA, slotX, slotY, cosA_eval, sinA_eval, cosR, sinR, IntervalExpr.eval]

def sum3A (f : Fin 3 → Aff) : Aff := Aff.add (f 0) (Aff.add (f 1) (f 2))
def sum3Q (f : Fin 3 → Quad) : Quad := Quad.add (f 0) (Quad.add (f 1) (f 2))

@[simp] theorem sum3A_eval (f : Fin 3 → Aff) (x : Fin 4 → ℝ) :
    (sum3A f).eval x = ∑ i, (f i).eval x := by
  simp [sum3A, Fin.sum_univ_three, add_assoc]

@[simp] theorem sum3Q_eval (f : Fin 3 → Quad) (x : Fin 4 → ℝ) :
    (sum3Q f).eval x = ∑ i, (f i).eval x := by
  simp [sum3Q, Fin.sum_univ_three, add_assoc]

namespace Certificate

def residualXA (C : Certificate) (i : Fin 3) : Aff :=
  sum3A fun s => Aff.add (Aff.smul (C.kappa i s 0) (slotXA s 0))
    (Aff.smul (C.kappa i s 1) (slotXA s 1))

def residualYA (C : Certificate) (i : Fin 3) : Aff :=
  sum3A fun s => Aff.add (Aff.smul (C.kappa i s 0) (slotYA s 0))
    (Aff.smul (C.kappa i s 1) (slotYA s 1))

end Certificate

/-- `cos (θ_q - θ_o)` and `sin (θ_q - θ_o)` as quadratic forms. -/
def cosDiff (o q : Fin 3) : Quad :=
  Quad.add ((cosA o).mul (cosA q)) ((sinA o).mul (sinA q))
def sinDiff (o q : Fin 3) : Quad :=
  Quad.add ((sinA q).mul (cosA o)) (Quad.smul (-1) ((cosA q).mul (sinA o)))

/-- Sign choice for `|sin (θ_other - θ_owner)|`: forced by the square fixed at
angle zero, by the region hypothesis, or by the midpoint value. -/
def widthSign (region : ℤ) (mid : Fin 4 → ℚ) (e : Fin 3) (a : Fin 4) : ℚ :=
  let o := axisOwner e a
  let q := axisOther e a
  if o = 0 then 1 else if q = 0 then -1
  else if region ≠ 0 then (if q = 1 then (region : ℚ) else -(region : ℚ))
  else
    let v := (sinDiff o q).value mid
    if 0 < v then 1 else if v < 0 then -1 else 0

def halfWidthQ (σ : ℚ) (e : Fin 3) (a : Fin 4) : Quad :=
  Quad.smul (1 / 2) (Quad.add (Aff.const 1).toQuad
    (Quad.add (cosDiff (axisOwner e a) (axisOther e a))
      (Quad.smul σ (sinDiff (axisOwner e a) (axisOther e a)))))

namespace Certificate

/-- The quadratic lower bound with the given sign choices. -/
def lowerQuad (C : Certificate) (σ : Fin 3 → ℚ) : Quad :=
  Quad.add (Quad.add (Aff.const (1 / 2)).toQuad
      (sum3Q fun e => Quad.smul (C.mu e) (halfWidthQ (σ e) e (C.axis e))))
    (Quad.smul (-1) (sum3Q fun i => Quad.smul (C.invWeight i)
      (Quad.add ((C.residualXA i).mul (C.residualXA i))
        ((C.residualYA i).mul (C.residualYA i)))))

/-- Region shift: a nonnegative multiple of `sin₁ - sin₂` (for `t₁ ≤ t₂`) or of
`sin₂ - sin₁` (for `t₂ ≤ t₁`), chosen from the midpoint gradient. -/
def shift (region : ℤ) (q : Quad) (mid : Fin 4 → ℚ) : Quad :=
  if region < 0 then
    Quad.add
      (Quad.smul (max 0 (-(q.grad mid 1))) (Aff.add (Aff.var 1) (Aff.var 3).neg).toQuad)
      (Quad.smul (max 0 (q.grad mid 0)) (Aff.add (Aff.var 2) (Aff.var 0).neg).toQuad)
  else if 0 < region then
    Quad.add
      (Quad.smul (max 0 (-(q.grad mid 3))) (Aff.add (Aff.var 3) (Aff.var 1).neg).toQuad)
      (Quad.smul (max 0 (q.grad mid 2)) (Aff.add (Aff.var 0) (Aff.var 2).neg).toQuad)
  else ⟨0, fun _ => 0, fun _ _ => 0⟩

def qcheck (C : Certificate) (B : RationalBox 4) (region : ℤ) : Bool :=
  let mid := Quad.midpoint B
  let L := C.lowerQuad (fun e => widthSign region mid e (C.axis e))
  C.wellFormed && decide (425 / 256 < (Quad.add L (shift region L mid)).lower B)

end Certificate

/- ## Soundness of the quadratic bound -/

private theorem abs_add_abs_ge (a b σ : ℝ) (hσ : σ = 1 ∨ σ = -1 ∨ σ = 0) :
    a + σ * b ≤ |a| + |b| := by
  rcases hσ with rfl | rfl | rfl
  · linarith [le_abs_self a, le_abs_self b]
  · linarith [le_abs_self a, neg_abs_le b]
  · linarith [le_abs_self a, abs_nonneg b]

theorem widthSign_cases (region : ℤ) (mid : Fin 4 → ℚ) (e : Fin 3) (a : Fin 4) :
    widthSign region mid e a = 1 ∨ widthSign region mid e a = -1 ∨
      widthSign region mid e a = 0 ∨ widthSign region mid e a = (region : ℚ) ∨
      widthSign region mid e a = -(region : ℚ) := by
  simp only [widthSign]
  by_cases h1 : axisOwner e a = 0
  · simp [h1]
  by_cases h2 : axisOther e a = 0
  · simp [h1, h2]
  by_cases h3 : region = 0
  · simp only [h1, h2, h3, if_false, ne_eq, not_true_eq_false]
    split_ifs <;> simp
  · by_cases h4 : axisOther e a = 1 <;> simp [h1, h2, h3, h4]

theorem halfWidthQ_le (x : Fin 4 → ℝ) (σ : ℚ) (hσ : σ = 1 ∨ σ = -1 ∨ σ = 0)
    (e : Fin 3) (a : Fin 4) :
    (halfWidthQ σ e a).eval x ≤ 1 / 2 * (1 + (widthE (axisOther e a) (axisU e a)
      (axisV e a)).eval x) := by
  have hU := axisU_eval x e a
  simp only [halfWidthQ, Quad.eval_smul, Quad.eval_add, Quad.eval_toQuad, Aff.eval_const,
    cosDiff, sinDiff, Quad.eval_mul, cosA_eval, sinA_eval, widthE_eval, hU.1, hU.2]
  push_cast
  have hσ' : (σ : ℝ) = 1 ∨ (σ : ℝ) = -1 ∨ (σ : ℝ) = 0 := by
    rcases hσ with h | h | h <;> simp [h]
  set o := axisOwner e a
  set q := axisOther e a
  rcases (show axisCol a = 0 ∨ axisCol a = 1 by
      rcases Fin.exists_fin_two.mp ⟨axisCol a, rfl⟩ with h | h <;> simp [h]) with hcol | hcol
  · rw [hcol]
    simp only [slotX, slotY, Matrix.cons_val_zero]
    change _ ≤ 1 / 2 * (1 + (|cosR x o * cosR x q + sinR x o * sinR x q| +
      |-(cosR x o * sinR x q) + sinR x o * cosR x q|))
    have := abs_add_abs_ge (cosR x o * cosR x q + sinR x o * sinR x q)
      (-(cosR x o * sinR x q) + sinR x o * cosR x q) (-σ)
      (by rcases hσ' with h | h | h <;> simp [h])
    nlinarith [this]
  · rw [hcol]
    simp only [slotX, slotY, Matrix.cons_val_one, Matrix.cons_val_zero]
    change _ ≤ 1 / 2 * (1 + (|(-sinR x o) * cosR x q + cosR x o * sinR x q| +
      |-((-sinR x o) * sinR x q) + cosR x o * cosR x q|))
    have := abs_add_abs_ge (-((-sinR x o) * sinR x q) + cosR x o * cosR x q)
      ((-sinR x o) * cosR x q + cosR x o * sinR x q) σ hσ'
    nlinarith [this]

theorem residualA_eval (C : Certificate) (x : Fin 4 → ℝ) (i : Fin 3) :
    (C.residualXA i).eval x = (C.residualXg i).eval x ∧
      (C.residualYA i).eval x = (C.residualYg i).eval x := by
  constructor <;>
    simp [Certificate.residualXA, Certificate.residualYA, Certificate.residualXg,
      Certificate.residualYg, IntervalExpr.eval, (slotA_eval x _ _).1, (slotA_eval x _ _).2]

def RegionHolds (region : ℤ) (t1 t2 : ℝ) : Prop := (region < 0 → t1 ≤ t2) ∧ (0 < region → t2 ≤ t1)

theorem lowerQuad_le (C : Certificate) (hC : C.wellFormed = true) (x : Fin 4 → ℝ)
    (σ : Fin 3 → ℚ) (hσ : ∀ e, σ e = 1 ∨ σ e = -1 ∨ σ e = 0) :
    (C.lowerQuad σ).eval x ≤ C.lowerBound.eval x := by
  have hmu (e : Fin 3) : (0 : ℝ) ≤ C.mu e := by
    have h : (∀ i : Fin 3, (((∀ k : Fin 4, 0 ≤ C.lam i k) ∧ 0 ≤ C.mu i) ∧ 0 ≤ C.invWeight i) ∧
        C.invWeight i * C.weight i = 1) ∧ C.weight 0 + C.weight 1 + C.weight 2 = 1 := by
      simpa [Certificate.wellFormed, List.all_eq_true] using hC
    exact_mod_cast (h.1 e).1.1.2
  have hw (e : Fin 3) := halfWidthQ_le x (σ e) (hσ e) e (C.axis e)
  have hr (i : Fin 3) := residualA_eval C x i
  simp only [Certificate.lowerQuad, Certificate.lowerBound, Quad.eval_add, Quad.eval_smul,
    Quad.eval_toQuad, Aff.eval_const, sum3Q_eval, sum3_eval, sub_eval, Quad.eval_mul,
    IntervalExpr.eval, halfWidthG, (hr _).1, (hr _).2, Fin.sum_univ_three]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left (hw 0) (hmu 0), mul_le_mul_of_nonneg_left (hw 1) (hmu 1),
    mul_le_mul_of_nonneg_left (hw 2) (hmu 2)]

theorem shift_nonpos (region : ℤ) (q : Quad) (mid : Fin 4 → ℚ) {t1 t2 : ℝ}
    (ht1 : 0 ≤ t1) (ht1' : t1 ≤ 1) (ht2 : 0 ≤ t2) (ht2' : t2 ≤ 1)
    (hreg : RegionHolds region t1 t2) :
    (Certificate.shift region q mid).eval (rotationVector t1 t2) ≤ 0 := by
  unfold Certificate.shift
  split_ifs with hneg hpos
  · simp only [Quad.eval_add, Quad.eval_smul, Quad.eval_toQuad, Aff.eval_add, Aff.eval_var,
      Aff.eval_neg]
    have h := rationalSin_monotone ht1 (hreg.1 hneg) ht2'
    have hc := rationalCos_antitone ht1 (hreg.1 hneg)
    simp only [rotationVector, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
    have hα : (0 : ℝ) ≤ (max 0 (-(q.grad mid 1)) : ℚ) := by exact_mod_cast le_max_left _ _
    have hβ : (0 : ℝ) ≤ (max 0 (q.grad mid 0) : ℚ) := by exact_mod_cast le_max_left _ _
    nlinarith
  · simp only [Quad.eval_add, Quad.eval_smul, Quad.eval_toQuad, Aff.eval_add, Aff.eval_var,
      Aff.eval_neg]
    have h := rationalSin_monotone ht2 (hreg.2 hpos) ht1'
    have hc := rationalCos_antitone ht2 (hreg.2 hpos)
    simp only [rotationVector, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
    have hα : (0 : ℝ) ≤ (max 0 (-(q.grad mid 3)) : ℚ) := by exact_mod_cast le_max_left _ _
    have hβ : (0 : ℝ) ≤ (max 0 (q.grad mid 2) : ℚ) := by exact_mod_cast le_max_left _ _
    nlinarith
  · simp [Quad.eval]

/-- One checked second-order certificate excludes its branch on its rotation
box intersected with its region. -/
theorem qcert_excludes (C : Certificate) {a1 b1 a2 b2 : ℚ} (region : ℤ)
    (hregion : region = -1 ∨ region = 0 ∨ region = 1)
    (hcheck : C.qcheck (rotationBox a1 b1 a2 b2) region = true)
    (P : SubcriticalRationalRotationPacking 3) (h0 : P.t 0 = 0) (hreal : Realizes P C.code)
    (hreg : RegionHolds region (P.t 1) (P.t 2))
    (ha1 : 0 ≤ (a1 : ℝ)) (ht1 : (a1 : ℝ) ≤ P.t 1 ∧ P.t 1 ≤ b1) (hb1 : (b1 : ℝ) ≤ 1)
    (ha2 : 0 ≤ (a2 : ℝ)) (ht2 : (a2 : ℝ) ≤ P.t 2 ∧ P.t 2 ≤ b2) (hb2 : (b2 : ℝ) ≤ 1) :
    False := by
  simp only [Certificate.qcheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨hwf, hlow⟩ := hcheck
  set x := rotationVector (P.t 1) (P.t 2)
  set B := rotationBox a1 b1 a2 b2
  have hxbox : B.Contains x := rotationVector_mem ha1 ht1 hb1 ha2 ht2 hb2
  set mid := Quad.midpoint B
  set σ : Fin 3 → ℚ := fun e => widthSign region mid e (C.axis e)
  have hσ (e : Fin 3) : σ e = 1 ∨ σ e = -1 ∨ σ e = 0 := by
    rcases widthSign_cases region mid e (C.axis e) with h | h | h | h | h <;>
      rcases hregion with rfl | rfl | rfl <;> simp_all [σ]
  have hL := lowerQuad_le C hwf x σ hσ
  have hle := lowerBound_le C hwf x
    (by simpa [x, rotationVector] using rational_rotation_unit (P.t 1))
    (by simpa [x, rotationVector] using rational_rotation_unit (P.t 2)) P.centers
    (by
      intro i k
      have hv := P.vertices i
      have hr := cosR_rotation P h0 i
      unfold StrictCandidateVertexInequalities at hv
      simp only [vertexSquared_rational] at hv
      unfold VertexBound
      rw [hr.1, hr.2]
      fin_cases k <;> simp only [cornerX_0, cornerX_1, cornerX_2, cornerX_3, cornerY_0,
        cornerY_1, cornerY_2, cornerY_3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        push_cast <;> linarith [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2])
    (fun e => hreal e)
  have hsh := shift_nonpos region (C.lowerQuad σ) mid (P.t_nonneg 1) (P.t_le_one 1)
    (P.t_nonneg 2) (P.t_le_one 2) hreg
  have hq := Quad.lower_le (Quad.add (C.lowerQuad σ) (Certificate.shift region
    (C.lowerQuad σ) mid)) hxbox
  rw [Quad.eval_add] at hq
  have hlow' : ((425 / 256 : ℚ) : ℝ) < ((Quad.add (C.lowerQuad σ)
      (Certificate.shift region (C.lowerQuad σ) mid)).lower B : ℚ) := by exact_mod_cast hlow
  push_cast at hlow'
  linarith

/- ## Trees with region splits -/

inductive QTree where
  | reject (l : Fin 3 → Fin 4 → ℕ) (m : Fin 3 → ℕ)
  | qreject (l : Fin 3 → Fin 4 → ℕ) (m : Fin 3 → ℕ)
  | keep
  | split (second : Bool) (left right : QTree)
  | diag (below above : QTree)

namespace QTree

/-- `region = -1`: `t₁ ≤ t₂`; `region = 1`: `t₂ ≤ t₁`; `0`: no hypothesis. -/
def check (code : ℕ) : QTree → TBox → ℤ → Bool
  | .reject l m, B, _ => (mkCert code l m).check (rotationBox B.a1 B.b1 B.a2 B.b2)
  | .qreject l m, B, region => (mkCert code l m).qcheck (rotationBox B.a1 B.b1 B.a2 B.b2) region
  | .keep, _, _ => true
  | .split second l r, B, region =>
      l.check code (B.left second) region && r.check code (B.right second) region
  | .diag l r, B, _ => l.check code B (-1) && r.check code B 1

def residuals : QTree → TBox → ℤ → List (TBox × ℤ)
  | .reject _ _, _, _ => []
  | .qreject _ _, _, _ => []
  | .keep, B, region => [(B, region)]
  | .split second l r, B, region =>
      l.residuals (B.left second) region ++ r.residuals (B.right second) region
  | .diag l r, B, _ => l.residuals B (-1) ++ r.residuals B 1

def ValidRegion (region : ℤ) : Prop := region = -1 ∨ region = 0 ∨ region = 1

theorem check_sound (T : QTree) (code : ℕ) (B : TBox) (region : ℤ) (hB : B.Inside)
    (hvr : ValidRegion region) (h : T.check code B region = true)
    (P : SubcriticalRationalRotationPacking 3) (h0 : P.t 0 = 0) (hreal : Realizes P code)
    (ht : B.Contains (P.t 1) (P.t 2)) (hreg : RegionHolds region (P.t 1) (P.t 2)) :
    ∃ R ∈ T.residuals B region, R.1.Contains (P.t 1) (P.t 2) ∧ ValidRegion R.2 ∧
      RegionHolds R.2 (P.t 1) (P.t 2) := by
  induction T generalizing B region with
  | reject l m =>
    exfalso
    obtain ⟨h1, h2, h3, h4⟩ := hB
    exact cert_excludes (mkCert code l m) h P h0 hreal (by exact_mod_cast h1)
      ⟨ht.1, ht.2.1⟩ (by exact_mod_cast h2) (by exact_mod_cast h3) ⟨ht.2.2.1, ht.2.2.2⟩
      (by exact_mod_cast h4)
  | qreject l m =>
    exfalso
    obtain ⟨h1, h2, h3, h4⟩ := hB
    exact qcert_excludes (mkCert code l m) region hvr h P h0 hreal hreg
      (by exact_mod_cast h1) ⟨ht.1, ht.2.1⟩ (by exact_mod_cast h2) (by exact_mod_cast h3)
      ⟨ht.2.2.1, ht.2.2.2⟩ (by exact_mod_cast h4)
  | keep => exact ⟨(B, region), by simp [residuals], ht, hvr, hreg⟩
  | split second l r hl hr =>
    simp only [check, Bool.and_eq_true] at h
    rcases B.split_covers second ht with hc | hc
    · obtain ⟨R, hR, hRc⟩ :=
        hl (B.left second) region (TBox.left_inside hB second hc) hvr h.1 hc hreg
      exact ⟨R, by simp [residuals, hR], hRc⟩
    · obtain ⟨R, hR, hRc⟩ :=
        hr (B.right second) region (TBox.right_inside hB second hc) hvr h.2 hc hreg
      exact ⟨R, by simp [residuals, hR], hRc⟩
  | diag l r hl hr =>
    simp only [check, Bool.and_eq_true] at h
    rcases le_total (P.t 1) (P.t 2) with h12 | h21
    · obtain ⟨R, hR, hRc⟩ := hl B (-1) hB (Or.inl rfl) h.1 ht
        ⟨fun _ => h12, fun h => absurd h (by norm_num)⟩
      exact ⟨R, by simp [residuals, hR], hRc⟩
    · obtain ⟨R, hR, hRc⟩ := hr B 1 hB (Or.inr (Or.inr rfl)) h.2 ht
        ⟨fun h => absurd h (by norm_num), fun _ => h21⟩
      exact ⟨R, by simp [residuals, hR], hRc⟩

end QTree

/-- A region-split tree labelled by its branch code. -/
structure CodedQTree where
  code : ℕ
  tree : QTree

theorem coded_qtrees_localize (L : List CodedQTree)
    (hcodes : L.map CodedQTree.code = List.range 512)
    (hcheck : ∀ T ∈ L, T.tree.check T.code TBox.unit 0 = true)
    (P : SubcriticalRationalRotationPacking 3) (h0 : P.t 0 = 0) :
    ∃ T ∈ L, Realizes P T.code ∧
      ∃ R ∈ T.tree.residuals TBox.unit 0, R.1.Contains (P.t 1) (P.t 2) ∧
        QTree.ValidRegion R.2 ∧ RegionHolds R.2 (P.t 1) (P.t 2) := by
  obtain ⟨code, hlt, hreal⟩ := exists_realized P h0
  have hmem : code ∈ L.map CodedQTree.code := by rw [hcodes]; simpa using hlt
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hmem
  refine ⟨T, hT, hreal, T.tree.check_sound T.code TBox.unit 0 ?_ (Or.inr (Or.inl rfl))
    (hcheck T hT) P h0 hreal ?_ ⟨fun h => absurd h (lt_irrefl 0), fun h => absurd h (lt_irrefl 0)⟩⟩
  · simp [TBox.Inside, TBox.unit]
  · exact ⟨by simpa [TBox.unit] using P.t_nonneg 1, by simpa [TBox.unit] using P.t_le_one 1,
      by simpa [TBox.unit] using P.t_nonneg 2, by simpa [TBox.unit] using P.t_le_one 2⟩

end

end CenterElimination
end ThreeSquares
