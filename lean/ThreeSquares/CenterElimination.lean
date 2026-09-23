import ThreeSquares.QuadrantSymmetry

/-! # Center-eliminating lower-bound certificates

For a fixed separation branch (one signed edge axis for each of the three
pairs), nonnegative rational vertex weights `λ` summing to one and
nonnegative separation weights `μ` give

`r² ≥ 1/2 + ∑ₑ μₑ Hₑ - ∑ᵢ ‖zᵢ - dᵢ/2‖² / wᵢ`.

The right side is obtained by completing the square in every center, so it
depends only on the cosines and sines of squares 1 and 2.  It is an interval
expression in four variables.  A rotation box on which every one of the 512
branches has a refuting certificate contains no packing below the candidate
radius.  No optimality, duality or floating-point claim is used: the weights
are data, and every inequality is checked by the kernel.
-/

namespace ThreeSquares
namespace CenterElimination

open scoped NNReal
open SquarePacking

noncomputable section

abbrev E := IntervalExpr 4

def sub (e f : E) : E := .add e (.neg f)
def sum3 (f : Fin 3 → E) : E := .add (f 0) (.add (f 1) (f 2))
def sum4 (f : Fin 4 → E) : E := .add (f 0) (.add (f 1) (.add (f 2) (f 3)))

/-- Variables: `cos₁, sin₁, cos₂, sin₂`; square 0 is axis-parallel. -/
def cosE : Fin 3 → E := ![.const 1, .var 0, .var 2]
def sinE : Fin 3 → E := ![.const 0, .var 1, .var 3]

def pairFst : Fin 3 → Fin 3 := ![0, 0, 1]
def pairSnd : Fin 3 → Fin 3 := ![1, 2, 2]

def cornerX : Fin 4 → ℚ := ![-1 / 2, -1 / 2, 1 / 2, 1 / 2]
def cornerY : Fin 4 → ℚ := ![-1 / 2, 1 / 2, -1 / 2, 1 / 2]

@[simp] theorem cornerX_0 : cornerX 0 = -1 / 2 := rfl
@[simp] theorem cornerX_1 : cornerX 1 = -1 / 2 := rfl
@[simp] theorem cornerX_2 : cornerX 2 = 1 / 2 := rfl
@[simp] theorem cornerX_3 : cornerX 3 = 1 / 2 := rfl
@[simp] theorem cornerY_0 : cornerY 0 = -1 / 2 := rfl
@[simp] theorem cornerY_1 : cornerY 1 = 1 / 2 := rfl
@[simp] theorem cornerY_2 : cornerY 2 = -1 / 2 := rfl
@[simp] theorem cornerY_3 : cornerY 3 = 1 / 2 := rfl

/-- The four edge axes in the order of `FourAxisSeparation`. -/
def axisU (e : Fin 3) : Fin 4 → E :=
  ![cosE (pairFst e), .neg (sinE (pairFst e)), cosE (pairSnd e), .neg (sinE (pairSnd e))]
def axisV (e : Fin 3) : Fin 4 → E :=
  ![sinE (pairFst e), cosE (pairFst e), sinE (pairSnd e), cosE (pairSnd e)]

/-- Twice the projected half-widths of one square on an axis. -/
def widthE (i : Fin 3) (u v : E) : E :=
  .add (.abs (.add (.mul u (cosE i)) (.mul v (sinE i))))
    (.abs (.add (.neg (.mul u (sinE i))) (.mul v (cosE i))))

def halfWidthE (e : Fin 3) (a : Fin 4) : E :=
  .mul (.const (1 / 2))
    (.add (widthE (pairFst e) (axisU e a) (axisV e a))
      (widthE (pairSnd e) (axisU e a) (axisV e a)))

/-- Frame columns of each square: `slotX s col, slotY s col` are the
coordinates of column `col` of the rotation of square `s`. -/
def slotX (s : Fin 3) : Fin 2 → E := ![cosE s, .neg (sinE s)]
def slotY (s : Fin 3) : Fin 2 → E := ![sinE s, cosE s]

/-- Square owning axis `a` of pair `e`, the other square, and the column. -/
def axisOwner (e : Fin 3) (a : Fin 4) : Fin 3 := if a.val < 2 then pairFst e else pairSnd e
def axisOther (e : Fin 3) (a : Fin 4) : Fin 3 := if a.val < 2 then pairSnd e else pairFst e
def axisCol (a : Fin 4) : Fin 2 := ⟨a.val % 2, Nat.mod_lt _ (by norm_num)⟩

/-- Half-width sum with the owner's exact projected width `1`. -/
def halfWidthG (e : Fin 3) (a : Fin 4) : E :=
  .mul (.const (1 / 2)) (.add (.const 1) (widthE (axisOther e a) (axisU e a) (axisV e a)))

/-- Branch code `((a₀·4 + a₁)·4 + a₂)·8 + s₀·4 + s₁·2 + s₂` for the axis
indices `aₑ` and the positive signs `sₑ`. -/
def axisOf (code : ℕ) : Fin 3 → Fin 4 :=
  ![⟨code / 128 % 4, Nat.mod_lt _ (by norm_num)⟩, ⟨code / 32 % 4, Nat.mod_lt _ (by norm_num)⟩,
    ⟨code / 8 % 4, Nat.mod_lt _ (by norm_num)⟩]

def signOf (code : ℕ) : Fin 3 → Bool :=
  ![decide (code / 4 % 2 = 1), decide (code / 2 % 2 = 1), decide (code % 2 = 1)]

def encode (a : Fin 3 → Fin 4) (s : Fin 3 → Bool) : ℕ :=
  ((a 0 * 4 + a 1) * 4 + a 2) * 8 + (s 0).toNat * 4 + (s 1).toNat * 2 + (s 2).toNat

theorem encode_lt (a : Fin 3 → Fin 4) (s : Fin 3 → Bool) : encode a s < 512 := by
  have h0 := (a 0).isLt; have h1 := (a 1).isLt; have h2 := (a 2).isLt
  have k0 := Bool.toNat_le (s 0); have k1 := Bool.toNat_le (s 1)
  have k2 := Bool.toNat_le (s 2)
  unfold encode; omega

private theorem decode_encode_aux : ∀ a0 a1 a2 : Fin 4, ∀ s0 s1 s2 : Bool,
    axisOf (encode ![a0, a1, a2] ![s0, s1, s2]) = ![a0, a1, a2] ∧
      signOf (encode ![a0, a1, a2] ![s0, s1, s2]) = ![s0, s1, s2] := by
  decide

theorem decode_encode (a : Fin 3 → Fin 4) (s : Fin 3 → Bool) :
    axisOf (encode a s) = a ∧ signOf (encode a s) = s := by
  have ha : a = ![a 0, a 1, a 2] := by ext i; fin_cases i <;> rfl
  have hs : s = ![s 0, s 1, s 2] := by ext i; fin_cases i <;> rfl
  rw [ha, hs]
  exact decode_encode_aux _ _ _ _ _ _

structure Certificate where
  code : ℕ
  lam : Fin 3 → Fin 4 → ℚ
  mu : Fin 3 → ℚ
  invWeight : Fin 3 → ℚ
  deriving DecidableEq

namespace Certificate

def axis (C : Certificate) : Fin 3 → Fin 4 := axisOf C.code
def sign (C : Certificate) : Fin 3 → Bool := signOf C.code

def weight (C : Certificate) (i : Fin 3) : ℚ := C.lam i 0 + C.lam i 1 + C.lam i 2 + C.lam i 3

def signedMu (C : Certificate) (e : Fin 3) : ℚ := if C.sign e then C.mu e else -C.mu e

/-- Coefficient of the signed separation `e` in the linear force on center `i`. -/
def coef (C : Certificate) (i e : Fin 3) : ℚ :=
  (if pairSnd e = i then C.signedMu e else 0) - (if pairFst e = i then C.signedMu e else 0)

def forceE (C : Certificate) (i : Fin 3) (u : Fin 3 → Fin 4 → E) : E :=
  sum3 fun e => .mul (.const (C.coef i e)) (u e (C.axis e))

def zetaX (C : Certificate) (i : Fin 3) : ℚ := ∑ k, C.lam i k * cornerX k
def zetaY (C : Certificate) (i : Fin 3) : ℚ := ∑ k, C.lam i k * cornerY k

def residualX (C : Certificate) (i : Fin 3) : E :=
  sub (sub (.mul (cosE i) (.const (C.zetaX i))) (.mul (sinE i) (.const (C.zetaY i))))
    (.mul (.const (1 / 2)) (C.forceE i axisU))

def residualY (C : Certificate) (i : Fin 3) : E :=
  sub (.add (.mul (sinE i) (.const (C.zetaX i))) (.mul (cosE i) (.const (C.zetaY i))))
    (.mul (.const (1 / 2)) (C.forceE i axisV))

/-- The center-free lower bound for the squared radius, in the form used by
the soundness proof. -/
def lowerBoundRaw (C : Certificate) : E :=
  sub (.add (.const (1 / 2)) (sum3 fun e => .mul (.const (C.mu e)) (halfWidthE e (C.axis e))))
    (sum3 fun i => .mul (.const (C.invWeight i))
      (.add (.square (C.residualX i)) (.square (C.residualY i))))

/- The checked form groups all coefficients of the same frame column before
interval evaluation, so exactly cancelling forces cancel in the enclosure, and
the owner of a separating axis has its exact projected width `1`. -/

/-- Contribution of separation `e` and the square's own vertex mean to the
coefficient of frame column `(s, col)` in the residual of square `i`. -/
def kappa (C : Certificate) (i s : Fin 3) (col : Fin 2) : ℚ :=
  (if s = i then (if col = 0 then C.zetaX i else C.zetaY i) else 0) -
    1 / 2 * ∑ e, (if axisOwner e (C.axis e) = s ∧ axisCol (C.axis e) = col
      then C.coef i e else 0)

def residualXg (C : Certificate) (i : Fin 3) : E :=
  sum3 fun s => .add (.mul (.const (C.kappa i s 0)) (slotX s 0))
    (.mul (.const (C.kappa i s 1)) (slotX s 1))

def residualYg (C : Certificate) (i : Fin 3) : E :=
  sum3 fun s => .add (.mul (.const (C.kappa i s 0)) (slotY s 0))
    (.mul (.const (C.kappa i s 1)) (slotY s 1))

/-- The checked center-free lower bound. -/
def lowerBound (C : Certificate) : E :=
  sub (.add (.const (1 / 2)) (sum3 fun e => .mul (.const (C.mu e)) (halfWidthG e (C.axis e))))
    (sum3 fun i => .mul (.const (C.invWeight i))
      (.add (.square (C.residualXg i)) (.square (C.residualYg i))))

def wellFormed (C : Certificate) : Bool :=
  (List.finRange 3).all (fun i =>
    (List.finRange 4).all (fun k => decide (0 ≤ C.lam i k)) &&
    decide (0 ≤ C.mu i) && decide (0 ≤ C.invWeight i) &&
    decide (C.invWeight i * C.weight i = 1)) &&
  decide (C.weight 0 + C.weight 1 + C.weight 2 = 1)

/-- The certificate refutes its branch on the four-variable box. -/
def check (C : Certificate) (B : RationalBox 4) : Bool :=
  C.wellFormed && IntervalFormula.refute B
    (.nonpos (sub C.lowerBound (.const (425 / 256))))

end Certificate

/- ## Completing the square -/

/-- Completing the square for one square with frame `(co, si)` and four
vertex weights. -/
theorem square_completion (c0 c1 co si d0 d1 iw : ℝ) (l : Fin 4 → ℝ)
    (hu : co ^ 2 + si ^ 2 = 1) (hw : iw * (l 0 + l 1 + l 2 + l 3) = 1) (hiw : 0 ≤ iw) :
    let zx := ∑ k, l k * (cornerX k : ℝ)
    let zy := ∑ k, l k * (cornerY k : ℝ)
    let r0 := (co * zx - si * zy) - 1 / 2 * d0
    let r1 := (si * zx + co * zy) - 1 / 2 * d1
    (l 0 + l 1 + l 2 + l 3) / 2 - iw * (r0 ^ 2 + r1 ^ 2) ≤
      (∑ k, l k * ((c0 + (co * cornerX k + -si * cornerY k)) ^ 2 +
        (c1 + (si * cornerX k + co * cornerY k)) ^ 2)) - (c0 * d0 + c1 * d1) := by
  intro zx zy r0 r1
  set w := l 0 + l 1 + l 2 + l 3
  have hzx : zx = (-(l 0) - l 1 + l 2 + l 3) / 2 := by
    simp only [zx, Fin.sum_univ_four, cornerX_0, cornerX_1, cornerX_2, cornerX_3]; push_cast; ring
  have hzy : zy = (-(l 0) + l 1 - l 2 + l 3) / 2 := by
    simp only [zy, Fin.sum_univ_four, cornerY_0, cornerY_1, cornerY_2, cornerY_3]; push_cast; ring
  have hsum : (∑ k, l k * ((c0 + (co * cornerX k + -si * cornerY k)) ^ 2 +
        (c1 + (si * cornerX k + co * cornerY k)) ^ 2)) =
      w * (c0 ^ 2 + c1 ^ 2) + 2 * (c0 * (co * zx - si * zy) + c1 * (si * zx + co * zy)) +
        (co ^ 2 + si ^ 2) * (w / 2) := by
    simp only [Fin.sum_univ_four, cornerX_0, cornerX_1, cornerX_2, cornerX_3, cornerY_0,
      cornerY_1, cornerY_2, cornerY_3, hzx, hzy, w]
    push_cast
    ring
  have key : ((∑ k, l k * ((c0 + (co * cornerX k + -si * cornerY k)) ^ 2 +
        (c1 + (si * cornerX k + co * cornerY k)) ^ 2)) - (c0 * d0 + c1 * d1)) -
      (w / 2 - iw * (r0 ^ 2 + r1 ^ 2)) =
      iw * ((w * c0 + r0) ^ 2 + (w * c1 + r1) ^ 2) := by
    rw [hsum]
    simp only [r0, r1]
    linear_combination (-(w * (c0 ^ 2 + c1 ^ 2) +
      2 * (c0 * ((co * zx - si * zy) - 1 / 2 * d0) +
        c1 * ((si * zx + co * zy) - 1 / 2 * d1)))) * hw + (w / 2) * hu
  have hnn : 0 ≤ iw * ((w * c0 + r0) ^ 2 + (w * c1 + r1) ^ 2) := by positivity
  linarith

/-- The exact form of `square_completion`, keeping the completed square. -/
theorem square_completion_disp (c0 c1 co si d0 d1 iw : ℝ) (l : Fin 4 → ℝ)
    (hu : co ^ 2 + si ^ 2 = 1) (hw : iw * (l 0 + l 1 + l 2 + l 3) = 1) :
    let zx := ∑ k, l k * (cornerX k : ℝ)
    let zy := ∑ k, l k * (cornerY k : ℝ)
    let r0 := (co * zx - si * zy) - 1 / 2 * d0
    let r1 := (si * zx + co * zy) - 1 / 2 * d1
    (l 0 + l 1 + l 2 + l 3) / 2 - iw * (r0 ^ 2 + r1 ^ 2) +
        iw * (((l 0 + l 1 + l 2 + l 3) * c0 + r0) ^ 2 + ((l 0 + l 1 + l 2 + l 3) * c1 + r1) ^ 2) =
      (∑ k, l k * ((c0 + (co * cornerX k + -si * cornerY k)) ^ 2 +
        (c1 + (si * cornerX k + co * cornerY k)) ^ 2)) - (c0 * d0 + c1 * d1) := by
  intro zx zy r0 r1
  set w := l 0 + l 1 + l 2 + l 3
  have hzx : zx = (-(l 0) - l 1 + l 2 + l 3) / 2 := by
    simp only [zx, Fin.sum_univ_four, cornerX_0, cornerX_1, cornerX_2, cornerX_3]; push_cast; ring
  have hzy : zy = (-(l 0) + l 1 - l 2 + l 3) / 2 := by
    simp only [zy, Fin.sum_univ_four, cornerY_0, cornerY_1, cornerY_2, cornerY_3]; push_cast; ring
  have hsum : (∑ k, l k * ((c0 + (co * cornerX k + -si * cornerY k)) ^ 2 +
        (c1 + (si * cornerX k + co * cornerY k)) ^ 2)) =
      w * (c0 ^ 2 + c1 ^ 2) + 2 * (c0 * (co * zx - si * zy) + c1 * (si * zx + co * zy)) +
        (co ^ 2 + si ^ 2) * (w / 2) := by
    simp only [Fin.sum_univ_four, cornerX_0, cornerX_1, cornerX_2, cornerX_3, cornerY_0,
      cornerY_1, cornerY_2, cornerY_3, hzx, hzy, w]
    push_cast
    ring
  rw [hsum]
  simp only [r0, r1]
  linear_combination (w * (c0 ^ 2 + c1 ^ 2) +
    2 * (c0 * ((co * zx - si * zy) - 1 / 2 * d0) +
      c1 * ((si * zx + co * zy) - 1 / 2 * d1))) * hw - (w / 2) * hu

/- ## Evaluation -/

section Eval

variable (x : Fin 4 → ℝ)

def cosR (i : Fin 3) : ℝ := (cosE i).eval x
def sinR (i : Fin 3) : ℝ := (sinE i).eval x

@[simp] theorem sum3_eval (f : Fin 3 → E) : (sum3 f).eval x = ∑ i, (f i).eval x := by
  simp [sum3, IntervalExpr.eval, Fin.sum_univ_three, add_assoc]

@[simp] theorem sub_eval (e f : E) : (sub e f).eval x = e.eval x - f.eval x := by
  simp [sub, IntervalExpr.eval, sub_eq_add_neg]

end Eval

/-- The real separation inequality selected by a branch for pair `e`. -/
def BranchSeparation (C : Certificate) (x : Fin 4 → ℝ) (c : Fin 3 → Plane) (e : Fin 3) : Prop :=
  let u := (axisU e (C.axis e)).eval x
  let v := (axisV e (C.axis e)).eval x
  let X := u * (c (pairSnd e) 0 - c (pairFst e) 0) + v * (c (pairSnd e) 1 - c (pairFst e) 1)
  (halfWidthE e (C.axis e)).eval x ≤ if C.sign e then X else -X

def VertexBound (x : Fin 4 → ℝ) (c : Fin 3 → Plane) (i : Fin 3) (k : Fin 4) : Prop :=
  (c i 0 + (cosR x i * cornerX k + -sinR x i * cornerY k)) ^ 2 +
    (c i 1 + (sinR x i * cornerX k + cosR x i * cornerY k)) ^ 2 ≤ 425 / 256

private theorem force_identity (C : Certificate) (x : Fin 4 → ℝ) (c : Fin 3 → Plane) :
    ∑ i, (c i 0 * (C.forceE i axisU).eval x + c i 1 * (C.forceE i axisV).eval x) =
      ∑ e, (C.signedMu e : ℝ) *
        ((axisU e (C.axis e)).eval x * (c (pairSnd e) 0 - c (pairFst e) 0) +
          (axisV e (C.axis e)).eval x * (c (pairSnd e) 1 - c (pairFst e) 1)) := by
  simp only [Certificate.forceE, sum3_eval, IntervalExpr.eval, Fin.sum_univ_three,
    Certificate.coef, pairFst, pairSnd]
  simp
  ring

/-- Soundness of the raw center-eliminated bound. -/
theorem lowerBoundRaw_le (C : Certificate) (hC : C.wellFormed = true) (x : Fin 4 → ℝ)
    (hu1 : x 0 ^ 2 + x 1 ^ 2 = 1) (hu2 : x 2 ^ 2 + x 3 ^ 2 = 1) (c : Fin 3 → Plane)
    (hv : ∀ i k, VertexBound x c i k) (hs : ∀ e, BranchSeparation C x c e) :
    C.lowerBoundRaw.eval x ≤ 425 / 256 := by
  have hwf : (∀ i : Fin 3, (∀ k : Fin 4, 0 ≤ C.lam i k) ∧ 0 ≤ C.mu i ∧ 0 ≤ C.invWeight i ∧
      C.invWeight i * C.weight i = 1) ∧ C.weight 0 + C.weight 1 + C.weight 2 = 1 := by
    have h : (∀ i : Fin 3, (((∀ k : Fin 4, 0 ≤ C.lam i k) ∧ 0 ≤ C.mu i) ∧ 0 ≤ C.invWeight i) ∧
        C.invWeight i * C.weight i = 1) ∧ C.weight 0 + C.weight 1 + C.weight 2 = 1 := by
      simpa [Certificate.wellFormed, List.all_eq_true] using hC
    refine ⟨fun i => ?_, h.2⟩
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h.1 i
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨hwf, hsum⟩ := hwf
  have hunit (i : Fin 3) : cosR x i ^ 2 + sinR x i ^ 2 = 1 := by
    fin_cases i <;> simp [cosR, sinR, cosE, sinE, IntervalExpr.eval, hu1, hu2]
  -- completing the square in each center
  have hsq (i : Fin 3) :=
    square_completion (c i 0) (c i 1) (cosR x i) (sinR x i)
      ((C.forceE i axisU).eval x) ((C.forceE i axisV).eval x) (C.invWeight i)
      (fun k => (C.lam i k : ℝ)) (hunit i)
      (by
        have := (hwf i).2.2.2
        simp only [Certificate.weight] at this
        exact_mod_cast this)
      (by exact_mod_cast (hwf i).2.2.1)
  -- vertex weights: the weighted mean of the squared vertex norms is at most S
  have hvert : ∑ i, ∑ k, (C.lam i k : ℝ) *
      ((c i 0 + (cosR x i * cornerX k + -sinR x i * cornerY k)) ^ 2 +
        (c i 1 + (sinR x i * cornerX k + cosR x i * cornerY k)) ^ 2) ≤ 425 / 256 := by
    calc _ ≤ ∑ i, ∑ k, (C.lam i k : ℝ) * (425 / 256) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_left (hv i k) (by exact_mod_cast (hwf i).1 k)
      _ = 425 / 256 := by
          have hs' : ((C.weight 0 + C.weight 1 + C.weight 2 : ℚ) : ℝ) = 1 := by
            exact_mod_cast hsum
          simp only [Certificate.weight] at hs'
          push_cast at hs'
          simp only [Fin.sum_univ_three, Fin.sum_univ_four]
          linear_combination (425 / 256 : ℝ) * hs'
  -- separation weights
  have hsep : ∑ e, (C.mu e : ℝ) * (halfWidthE e (C.axis e)).eval x ≤
      ∑ e, (C.signedMu e : ℝ) *
        ((axisU e (C.axis e)).eval x * (c (pairSnd e) 0 - c (pairFst e) 0) +
          (axisV e (C.axis e)).eval x * (c (pairSnd e) 1 - c (pairFst e) 1)) := by
    apply Finset.sum_le_sum; intro e _
    have h := hs e
    have hmu : (0 : ℝ) ≤ C.mu e := by exact_mod_cast (hwf e).2.1
    simp only [BranchSeparation] at h
    unfold Certificate.signedMu
    split_ifs at h ⊢ with hsg
    · exact mul_le_mul_of_nonneg_left h hmu
    · push_cast
      nlinarith [mul_le_mul_of_nonneg_left h hmu]
  have hforce := force_identity C x c
  have hw' : ((C.weight 0 + C.weight 1 + C.weight 2 : ℚ) : ℝ) = 1 := by exact_mod_cast hsum
  simp only [Certificate.weight] at hw'
  push_cast at hw'
  have h0 := hsq 0
  have h1 := hsq 1
  have h2 := hsq 2
  simp only at h0 h1 h2
  simp only [Certificate.lowerBoundRaw, sub_eval, sum3_eval, IntervalExpr.eval,
    Certificate.residualX, Certificate.residualY, Certificate.zetaX, Certificate.zetaY]
  push_cast
  simp only [Fin.sum_univ_three] at hvert hsep hforce ⊢
  simp only [cosR, sinR] at h0 h1 h2 hvert
  linarith

/-- The completed squares are bounded by the slack of the raw bound. -/
theorem lowerBoundRaw_disp (C : Certificate) (hC : C.wellFormed = true) (x : Fin 4 → ℝ)
    (hu1 : x 0 ^ 2 + x 1 ^ 2 = 1) (hu2 : x 2 ^ 2 + x 3 ^ 2 = 1) (c : Fin 3 → Plane)
    (hv : ∀ i k, VertexBound x c i k) (hs : ∀ e, BranchSeparation C x c e) :
    C.lowerBoundRaw.eval x + ∑ i, (C.invWeight i : ℝ) *
      (((C.weight i : ℝ) * c i 0 + (C.residualX i).eval x) ^ 2 +
        ((C.weight i : ℝ) * c i 1 + (C.residualY i).eval x) ^ 2) ≤ 425 / 256 := by
  have hwf : (∀ i : Fin 3, (∀ k : Fin 4, 0 ≤ C.lam i k) ∧ 0 ≤ C.mu i ∧ 0 ≤ C.invWeight i ∧
      C.invWeight i * C.weight i = 1) ∧ C.weight 0 + C.weight 1 + C.weight 2 = 1 := by
    have h : (∀ i : Fin 3, (((∀ k : Fin 4, 0 ≤ C.lam i k) ∧ 0 ≤ C.mu i) ∧ 0 ≤ C.invWeight i) ∧
        C.invWeight i * C.weight i = 1) ∧ C.weight 0 + C.weight 1 + C.weight 2 = 1 := by
      simpa [Certificate.wellFormed, List.all_eq_true] using hC
    refine ⟨fun i => ?_, h.2⟩
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h.1 i
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨hwf, hsum⟩ := hwf
  have hunit (i : Fin 3) : cosR x i ^ 2 + sinR x i ^ 2 = 1 := by
    fin_cases i <;> simp [cosR, sinR, cosE, sinE, IntervalExpr.eval, hu1, hu2]
  have hsq (i : Fin 3) :=
    square_completion_disp (c i 0) (c i 1) (cosR x i) (sinR x i)
      ((C.forceE i axisU).eval x) ((C.forceE i axisV).eval x) (C.invWeight i)
      (fun k => (C.lam i k : ℝ)) (hunit i)
      (by
        have := (hwf i).2.2.2
        simp only [Certificate.weight] at this
        exact_mod_cast this)
  have hvert : ∑ i, ∑ k, (C.lam i k : ℝ) *
      ((c i 0 + (cosR x i * cornerX k + -sinR x i * cornerY k)) ^ 2 +
        (c i 1 + (sinR x i * cornerX k + cosR x i * cornerY k)) ^ 2) ≤ 425 / 256 := by
    calc _ ≤ ∑ i, ∑ k, (C.lam i k : ℝ) * (425 / 256) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_left (hv i k) (by exact_mod_cast (hwf i).1 k)
      _ = 425 / 256 := by
          have hs' : ((C.weight 0 + C.weight 1 + C.weight 2 : ℚ) : ℝ) = 1 := by
            exact_mod_cast hsum
          simp only [Certificate.weight] at hs'
          push_cast at hs'
          simp only [Fin.sum_univ_three, Fin.sum_univ_four]
          linear_combination (425 / 256 : ℝ) * hs'
  have hsep : ∑ e, (C.mu e : ℝ) * (halfWidthE e (C.axis e)).eval x ≤
      ∑ e, (C.signedMu e : ℝ) *
        ((axisU e (C.axis e)).eval x * (c (pairSnd e) 0 - c (pairFst e) 0) +
          (axisV e (C.axis e)).eval x * (c (pairSnd e) 1 - c (pairFst e) 1)) := by
    apply Finset.sum_le_sum; intro e _
    have h := hs e
    have hmu : (0 : ℝ) ≤ C.mu e := by exact_mod_cast (hwf e).2.1
    simp only [BranchSeparation] at h
    unfold Certificate.signedMu
    split_ifs at h ⊢ with hsg
    · exact mul_le_mul_of_nonneg_left h hmu
    · push_cast
      nlinarith [mul_le_mul_of_nonneg_left h hmu]
  have hforce := force_identity C x c
  have hw' : ((C.weight 0 + C.weight 1 + C.weight 2 : ℚ) : ℝ) = 1 := by exact_mod_cast hsum
  simp only [Certificate.weight] at hw' ⊢
  push_cast at hw'
  have h0 := hsq 0
  have h1 := hsq 1
  have h2 := hsq 2
  simp only at h0 h1 h2
  simp only [Certificate.lowerBoundRaw, sub_eval, sum3_eval, IntervalExpr.eval,
    Certificate.residualX, Certificate.residualY, Certificate.zetaX, Certificate.zetaY]
  push_cast
  simp only [Fin.sum_univ_three] at hvert hsep hforce ⊢
  simp only [cosR, sinR] at h0 h1 h2 hvert
  linarith

/- ## The grouped form evaluates to the raw bound -/

private theorem slot_pick (o : Fin 3) (cc : Fin 2) (q : ℚ) (g : Fin 3 → Fin 2 → ℝ) :
    ∑ s, ∑ col, (((if o = s ∧ cc = col then q else 0 : ℚ)) : ℝ) * g s col = q * g o cc := by
  fin_cases o <;> fin_cases cc <;> simp [Fin.sum_univ_three, Fin.sum_univ_two]

theorem axisU_eval (x : Fin 4 → ℝ) (e : Fin 3) (a : Fin 4) :
    (axisU e a).eval x = (slotX (axisOwner e a) (axisCol a)).eval x ∧
      (axisV e a).eval x = (slotY (axisOwner e a) (axisCol a)).eval x := by
  fin_cases a <;> simp [axisU, axisV, slotX, slotY, axisOwner, axisCol]

private theorem self_pick (i : Fin 3) (a b : ℚ) (g : Fin 3 → Fin 2 → ℝ) :
    ∑ s, ∑ col, (((if s = i then (if col = 0 then a else b) else 0 : ℚ)) : ℝ) * g s col =
      a * g i 0 + b * g i 1 := by
  fin_cases i <;> simp [Fin.sum_univ_three, Fin.sum_univ_two]

private theorem residual_grouped (C : Certificate) (x : Fin 4 → ℝ) (i : Fin 3)
    (slot : Fin 3 → Fin 2 → E) (u : Fin 3 → Fin 4 → E) (z : ℝ)
    (hu : ∀ e a, (u e a).eval x = (slot (axisOwner e a) (axisCol a)).eval x)
    (hz : (C.zetaX i : ℝ) * (slot i 0).eval x + (C.zetaY i : ℝ) * (slot i 1).eval x = z) :
    (sum3 fun s => IntervalExpr.add (.mul (.const (C.kappa i s 0)) (slot s 0))
      (.mul (.const (C.kappa i s 1)) (slot s 1))).eval x =
      z - 1 / 2 * ∑ e, (C.coef i e : ℝ) * (u e (C.axis e)).eval x := by
  set g : Fin 3 → Fin 2 → ℝ := fun s col => (slot s col).eval x
  have hpick (e : Fin 3) := slot_pick (axisOwner e (C.axis e)) (axisCol (C.axis e))
    (C.coef i e) g
  have hA := self_pick i (C.zetaX i) (C.zetaY i) g
  have hexp : (sum3 fun s => IntervalExpr.add (.mul (.const (C.kappa i s 0)) (slot s 0))
      (.mul (.const (C.kappa i s 1)) (slot s 1))).eval x =
      ∑ s, ∑ col, (C.kappa i s col : ℝ) * g s col := by
    simp [sum3_eval, IntervalExpr.eval, Fin.sum_univ_two, g]
  have hsplit : ∑ s, ∑ col, (C.kappa i s col : ℝ) * g s col =
      ∑ s, ∑ col, (((if s = i then (if col = 0 then C.zetaX i else C.zetaY i) else 0 : ℚ)) : ℝ) *
          g s col -
        1 / 2 * ∑ e, ∑ s, ∑ col,
          (((if axisOwner e (C.axis e) = s ∧ axisCol (C.axis e) = col then C.coef i e
            else 0 : ℚ)) : ℝ) * g s col := by
    simp only [Certificate.kappa, Fin.sum_univ_three, Fin.sum_univ_two]
    push_cast
    ring
  rw [hexp, hsplit, hA]
  simp only [hpick, hu, ← hz, g]

theorem widthE_eval (x : Fin 4 → ℝ) (i : Fin 3) (u v : E) :
    (widthE i u v).eval x = |u.eval x * cosR x i + v.eval x * sinR x i| +
      |-(u.eval x * sinR x i) + v.eval x * cosR x i| := rfl

theorem width_self (x : Fin 4 → ℝ) (s : Fin 3) (col : Fin 2)
    (hu : cosR x s ^ 2 + sinR x s ^ 2 = 1) :
    |(slotX s col).eval x * cosR x s + (slotY s col).eval x * sinR x s| +
      |-((slotX s col).eval x * sinR x s) + (slotY s col).eval x * cosR x s| = 1 := by
  fin_cases col
  · simp only [slotX, slotY, Fin.zero_eta, Matrix.cons_val_zero]
    change |cosR x s * cosR x s + sinR x s * sinR x s| +
      |-(cosR x s * sinR x s) + sinR x s * cosR x s| = 1
    rw [show cosR x s * cosR x s + sinR x s * sinR x s = 1 by nlinarith,
      show -(cosR x s * sinR x s) + sinR x s * cosR x s = 0 by ring]
    simp
  · simp only [slotX, slotY, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    change |-sinR x s * cosR x s + cosR x s * sinR x s| +
      |-(-sinR x s * sinR x s) + cosR x s * cosR x s| = 1
    rw [show -sinR x s * cosR x s + cosR x s * sinR x s = 0 by ring,
      show -(-sinR x s * sinR x s) + cosR x s * cosR x s = 1 by nlinarith]
    simp

theorem halfWidthG_eval (x : Fin 4 → ℝ) (hu1 : x 0 ^ 2 + x 1 ^ 2 = 1)
    (hu2 : x 2 ^ 2 + x 3 ^ 2 = 1) (e : Fin 3) (a : Fin 4) :
    (halfWidthG e a).eval x = (halfWidthE e a).eval x := by
  have hunit (i : Fin 3) : cosR x i ^ 2 + sinR x i ^ 2 = 1 := by
    fin_cases i <;> simp [cosR, sinR, cosE, sinE, IntervalExpr.eval, hu1, hu2]
  have hself := width_self x (axisOwner e a) (axisCol a) (hunit _)
  rw [← (axisU_eval x e a).1, ← (axisU_eval x e a).2] at hself
  simp only [halfWidthG, halfWidthE, IntervalExpr.eval, widthE_eval] at hself ⊢
  by_cases ha : a.val < 2
  · simp only [axisOwner, axisOther, ha, if_true] at hself ⊢
    rw [hself]; push_cast; ring
  · simp only [axisOwner, axisOther, ha, if_false] at hself ⊢
    rw [hself]; push_cast; ring

theorem residualXg_eval (C : Certificate) (x : Fin 4 → ℝ) (i : Fin 3) :
    (C.residualXg i).eval x = (C.residualX i).eval x ∧
      (C.residualYg i).eval x = (C.residualY i).eval x := by
  constructor
  · rw [Certificate.residualXg, residual_grouped C x i slotX axisU
      ((cosE i).eval x * C.zetaX i - (sinE i).eval x * C.zetaY i)
      (fun e a => (axisU_eval x e a).1) (by simp [slotX, IntervalExpr.eval]; ring)]
    simp [Certificate.residualX, Certificate.forceE, IntervalExpr.eval]
  · rw [Certificate.residualYg, residual_grouped C x i slotY axisV
      ((sinE i).eval x * C.zetaX i + (cosE i).eval x * C.zetaY i)
      (fun e a => (axisU_eval x e a).2) (by simp [slotY]; ring)]
    simp [Certificate.residualY, Certificate.forceE, IntervalExpr.eval]

theorem lowerBound_eval (C : Certificate) (x : Fin 4 → ℝ) (hu1 : x 0 ^ 2 + x 1 ^ 2 = 1)
    (hu2 : x 2 ^ 2 + x 3 ^ 2 = 1) : C.lowerBound.eval x = C.lowerBoundRaw.eval x := by
  simp only [Certificate.lowerBound, Certificate.lowerBoundRaw, sub_eval, sum3_eval,
    IntervalExpr.eval, (residualXg_eval C x _).1, (residualXg_eval C x _).2,
    halfWidthG_eval x hu1 hu2]

/-- Soundness of one center-eliminating certificate. -/
theorem lowerBound_le (C : Certificate) (hC : C.wellFormed = true) (x : Fin 4 → ℝ)
    (hu1 : x 0 ^ 2 + x 1 ^ 2 = 1) (hu2 : x 2 ^ 2 + x 3 ^ 2 = 1) (c : Fin 3 → Plane)
    (hv : ∀ i k, VertexBound x c i k) (hs : ∀ e, BranchSeparation C x c e) :
    C.lowerBound.eval x ≤ 425 / 256 := by
  rw [lowerBound_eval C x hu1 hu2]
  exact lowerBoundRaw_le C hC x hu1 hu2 c hv hs

/- ## Rotation boxes -/

/-- The four-variable box of cosines and sines for rotation parameters in
`[a₁,b₁] × [a₂,b₂]`. -/
def ratCos (t : ℚ) : ℚ := (1 - t ^ 2) / (1 + t ^ 2)
def ratSin (t : ℚ) : ℚ := 2 * t / (1 + t ^ 2)

def rotationBox (a1 b1 a2 b2 : ℚ) : RationalBox 4 :=
  ![⟨ratCos b1, ratCos a1⟩, ⟨ratSin a1, ratSin b1⟩, ⟨ratCos b2, ratCos a2⟩, ⟨ratSin a2, ratSin b2⟩]

theorem rationalCos_antitone {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    rationalCos t ≤ rationalCos s := by
  unfold rationalCos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hst), sub_nonneg.mpr hst]

theorem rationalSin_monotone {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    rationalSin s ≤ rationalSin t := by
  unfold rationalSin
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr (show s * t ≤ 1 by nlinarith))]

private theorem ratCos_cast (q : ℚ) : ((ratCos q : ℚ) : ℝ) = rationalCos q := by
  simp [ratCos, rationalCos]

private theorem ratSin_cast (q : ℚ) : ((ratSin q : ℚ) : ℝ) = rationalSin q := by
  simp [ratSin, rationalSin]

def rotationVector (t1 t2 : ℝ) : Fin 4 → ℝ :=
  ![rationalCos t1, rationalSin t1, rationalCos t2, rationalSin t2]

theorem rotationVector_mem {a1 b1 a2 b2 : ℚ} {t1 t2 : ℝ}
    (ha1 : 0 ≤ (a1 : ℝ)) (h1 : (a1 : ℝ) ≤ t1 ∧ t1 ≤ b1) (hb1 : (b1 : ℝ) ≤ 1)
    (ha2 : 0 ≤ (a2 : ℝ)) (h2 : (a2 : ℝ) ≤ t2 ∧ t2 ≤ b2) (hb2 : (b2 : ℝ) ≤ 1) :
    (rotationBox a1 b1 a2 b2).Contains (rotationVector t1 t2) := by
  intro k
  fin_cases k
  · show ((ratCos b1 : ℚ) : ℝ) ≤ rationalCos t1 ∧ rationalCos t1 ≤ ((ratCos a1 : ℚ) : ℝ)
    rw [ratCos_cast, ratCos_cast]
    exact ⟨rationalCos_antitone (ha1.trans h1.1) h1.2, rationalCos_antitone ha1 h1.1⟩
  · show ((ratSin a1 : ℚ) : ℝ) ≤ rationalSin t1 ∧ rationalSin t1 ≤ ((ratSin b1 : ℚ) : ℝ)
    rw [ratSin_cast, ratSin_cast]
    exact ⟨rationalSin_monotone ha1 h1.1 (h1.2.trans hb1),
      rationalSin_monotone (ha1.trans h1.1) h1.2 hb1⟩
  · show ((ratCos b2 : ℚ) : ℝ) ≤ rationalCos t2 ∧ rationalCos t2 ≤ ((ratCos a2 : ℚ) : ℝ)
    rw [ratCos_cast, ratCos_cast]
    exact ⟨rationalCos_antitone (ha2.trans h2.1) h2.2, rationalCos_antitone ha2 h2.1⟩
  · show ((ratSin a2 : ℚ) : ℝ) ≤ rationalSin t2 ∧ rationalSin t2 ≤ ((ratSin b2 : ℚ) : ℝ)
    rw [ratSin_cast, ratSin_cast]
    exact ⟨rationalSin_monotone ha2 h2.1 (h2.2.trans hb2),
      rationalSin_monotone (ha2.trans h2.1) h2.2 hb2⟩

/- ## Excluding a rotation box -/

/-- All 512 branches, in code order, are refuted on the rotation box. -/
def excludesBox (a1 b1 a2 b2 : ℚ) (certs : List Certificate) : Bool :=
  decide (0 ≤ a1) && decide (b1 ≤ 1) && decide (0 ≤ a2) && decide (b2 ≤ 1) &&
  decide (certs.map Certificate.code = List.range 512) &&
  certs.all (fun C => C.check (rotationBox a1 b1 a2 b2))

theorem vertexSquared_rational (c : Plane) (t : ℝ) (x y : ℝ) :
    vertexSquared c (rationalRotationCoefficients t) x y =
      (c 0 + (rationalCos t * x + -rationalSin t * y)) ^ 2 +
        (c 1 + (rationalSin t * x + rationalCos t * y)) ^ 2 := rfl

theorem cosR_rotation (P : SubcriticalRationalRotationPacking 3) (h0 : P.t 0 = 0)
    (i : Fin 3) : cosR (rotationVector (P.t 1) (P.t 2)) i = rationalCos (P.t i) ∧
      sinR (rotationVector (P.t 1) (P.t 2)) i = rationalSin (P.t i) := by
  fin_cases i <;>
    simp [cosR, sinR, cosE, sinE, IntervalExpr.eval, rotationVector, h0, rationalCos,
      rationalSin]

private theorem axis_exists (x : Fin 4 → ℝ) (c : Fin 3 → Plane) (e : Fin 3)
    (h : ∃ a : Fin 4, (halfWidthE e a).eval x ≤
      |(axisU e a).eval x * (c (pairSnd e) 0 - c (pairFst e) 0) +
        (axisV e a).eval x * (c (pairSnd e) 1 - c (pairFst e) 1)|) :
    ∃ a : Fin 4, ∃ σ : Bool, (halfWidthE e a).eval x ≤
      (if σ then (axisU e a).eval x * (c (pairSnd e) 0 - c (pairFst e) 0) +
        (axisV e a).eval x * (c (pairSnd e) 1 - c (pairFst e) 1) else
        -((axisU e a).eval x * (c (pairSnd e) 0 - c (pairFst e) 0) +
        (axisV e a).eval x * (c (pairSnd e) 1 - c (pairFst e) 1))) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, decide (0 ≤ (axisU e a).eval x * (c (pairSnd e) 0 - c (pairFst e) 0) +
        (axisV e a).eval x * (c (pairSnd e) 1 - c (pairFst e) 1)), ?_⟩
  split_ifs with hX
  · simpa [abs_of_nonneg (of_decide_eq_true hX)] using ha
  · have hX' := lt_of_not_ge (fun h => hX (decide_eq_true h))
    simpa [abs_of_neg hX'] using ha

/-- The four-axis separation of one pair, rewritten through the interval
expressions of the certificate language. -/
private theorem pair_axis (P : SubcriticalRationalRotationPacking 3) (h0 : P.t 0 = 0)
    (e : Fin 3) : ∃ a : Fin 4,
      (halfWidthE e a).eval (rotationVector (P.t 1) (P.t 2)) ≤
        |(axisU e a).eval (rotationVector (P.t 1) (P.t 2)) *
            (P.centers (pairSnd e) 0 - P.centers (pairFst e) 0) +
          (axisV e a).eval (rotationVector (P.t 1) (P.t 2)) *
            (P.centers (pairSnd e) 1 - P.centers (pairFst e) 1)| := by
  have hlt : pairFst e < pairSnd e := by fin_cases e <;> decide
  have hsep := P.separations _ _ hlt
  have hi := cosR_rotation P h0 (pairFst e)
  have hj := cosR_rotation P h0 (pairSnd e)
  simp only [cosR, sinR] at hi hj
  unfold FourAxisSeparation AxisInequality at hsep
  simp only [rationalRotationCoefficients, rotationCoefficients] at hsep
  rcases hsep with h | h | h | h
  · refine ⟨0, ?_⟩
    simp only [halfWidthE, widthE, axisU, axisV, IntervalExpr.eval, Matrix.cons_val_zero,
      hi.1, hi.2, hj.1, hj.2]
    convert h using 2
    push_cast
    ring_nf
  · refine ⟨1, ?_⟩
    simp only [halfWidthE, widthE, axisU, axisV, IntervalExpr.eval, Matrix.cons_val_one,
      Matrix.cons_val_zero, hi.1, hi.2, hj.1, hj.2]
    convert h using 2
    push_cast
    ring_nf
  · refine ⟨2, ?_⟩
    simp only [halfWidthE, widthE, axisU, axisV, IntervalExpr.eval, hi.1, hi.2, hj.1, hj.2]
    simp only [Matrix.cons_val, hj.1, hj.2]
    convert h using 2
    push_cast
    ring_nf
  · refine ⟨3, ?_⟩
    simp only [halfWidthE, widthE, axisU, axisV, IntervalExpr.eval, hi.1, hi.2, hj.1, hj.2]
    simp only [Matrix.cons_val]
    simp only [IntervalExpr.eval, hj.1, hj.2]
    convert h using 2
    push_cast
    ring_nf

/-- A checked family of 512 center-eliminating certificates excludes every
subcritical normalized packing whose rotation parameters lie in the box. -/
theorem excludesBox_sound {a1 b1 a2 b2 : ℚ} {certs : List Certificate}
    (h : excludesBox a1 b1 a2 b2 certs = true)
    (P : SubcriticalRationalRotationPacking 3) (h0 : P.t 0 = 0)
    (ht1 : (a1 : ℝ) ≤ P.t 1 ∧ P.t 1 ≤ b1) (ht2 : (a2 : ℝ) ≤ P.t 2 ∧ P.t 2 ≤ b2) : False := by
  simp only [excludesBox, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨ha1, hb1⟩, ha2⟩, hb2⟩, hcodes⟩, hchecks⟩ := h
  set x := rotationVector (P.t 1) (P.t 2)
  set c := P.centers
  -- choose the branch realized by the packing
  have hbranch (e : Fin 3) := axis_exists x c e (pair_axis P h0 e)
  choose a σ hσ using hbranch
  set code := encode a σ
  have hcode : code < 512 := encode_lt a σ
  have hlen : certs.length = 512 := by
    simpa using congrArg List.length hcodes
  let C := certs[code]'(by omega)
  have hC : C.code = code := by
    have := congrArg (fun l => l[code]?) hcodes
    simp only [List.getElem?_map, List.getElem?_range hcode] at this
    rw [List.getElem?_eq_getElem (by omega)] at this
    simpa using this
  have hax : C.axis = a := by
    simp only [Certificate.axis, hC]; exact (decode_encode a σ).1
  have hsg : C.sign = σ := by
    simp only [Certificate.sign, hC]; exact (decode_encode a σ).2
  have hcheck : C.check (rotationBox a1 b1 a2 b2) = true :=
    hchecks C (List.getElem_mem _)
  simp only [Certificate.check, Bool.and_eq_true] at hcheck
  have hxbox : (rotationBox a1 b1 a2 b2).Contains x :=
    rotationVector_mem (by exact_mod_cast ha1) ht1 (by exact_mod_cast hb1)
      (by exact_mod_cast ha2) ht2 (by exact_mod_cast hb2)
  have hle := lowerBound_le C hcheck.1 x
    (by simpa [x, rotationVector] using rational_rotation_unit (P.t 1))
    (by simpa [x, rotationVector] using rational_rotation_unit (P.t 2)) c
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
    (by
      intro e
      unfold BranchSeparation
      rw [hax, hsg]
      exact hσ e)
  apply IntervalFormula.refute_sound _ hxbox hcheck.2
  change (sub C.lowerBound (.const (425 / 256))).eval x ≤ 0
  rw [sub_eval]
  simp only [IntervalExpr.eval]
  push_cast
  linarith

/- ## Branch realization and single certificates -/

/-- The packing satisfies the signed separation branch encoded by `code`. -/
def Realizes (P : SubcriticalRationalRotationPacking 3) (code : ℕ) : Prop :=
  ∀ e, BranchSeparation ⟨code, fun _ _ => 0, fun _ => 0, fun _ => 0⟩
    (rotationVector (P.t 1) (P.t 2)) P.centers e

theorem exists_realized (P : SubcriticalRationalRotationPacking 3) (h0 : P.t 0 = 0) :
    ∃ code < 512, Realizes P code := by
  have hbranch (e : Fin 3) :=
    axis_exists (rotationVector (P.t 1) (P.t 2)) P.centers e (pair_axis P h0 e)
  choose a σ hσ using hbranch
  refine ⟨encode a σ, encode_lt a σ, fun e => ?_⟩
  unfold BranchSeparation
  simp only [Certificate.axis, Certificate.sign, (decode_encode a σ).1, (decode_encode a σ).2]
  exact hσ e

/-- One checked certificate excludes its branch on its rotation box. -/
theorem cert_excludes (C : Certificate) {a1 b1 a2 b2 : ℚ}
    (hcheck : C.check (rotationBox a1 b1 a2 b2) = true)
    (P : SubcriticalRationalRotationPacking 3) (h0 : P.t 0 = 0) (hreal : Realizes P C.code)
    (ha1 : 0 ≤ (a1 : ℝ)) (ht1 : (a1 : ℝ) ≤ P.t 1 ∧ P.t 1 ≤ b1) (hb1 : (b1 : ℝ) ≤ 1)
    (ha2 : 0 ≤ (a2 : ℝ)) (ht2 : (a2 : ℝ) ≤ P.t 2 ∧ P.t 2 ≤ b2) (hb2 : (b2 : ℝ) ≤ 1) :
    False := by
  simp only [Certificate.check, Bool.and_eq_true] at hcheck
  set x := rotationVector (P.t 1) (P.t 2)
  have hxbox : (rotationBox a1 b1 a2 b2).Contains x :=
    rotationVector_mem ha1 ht1 hb1 ha2 ht2 hb2
  have hle := lowerBound_le C hcheck.1 x
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
  apply IntervalFormula.refute_sound _ hxbox hcheck.2
  change (sub C.lowerBound (.const (425 / 256))).eval x ≤ 0
  rw [sub_eval]
  simp only [IntervalExpr.eval]
  push_cast
  linarith

/- ## Certificate trees over the rotation square -/

/-- Compact certificate data: all weights are integers over `2¹⁶`; the
inverse vertex weights are computed by the checker. -/
def mkCert (code : ℕ) (l : Fin 3 → Fin 4 → ℕ) (m : Fin 3 → ℕ) : Certificate where
  code := code
  lam i k := (l i k : ℚ) / 65536
  mu e := (m e : ℚ) / 65536
  invWeight i := 65536 / ((l i 0 + l i 1 + l i 2 + l i 3 : ℕ) : ℚ)

inductive BranchTree where
  | reject (l : Fin 3 → Fin 4 → ℕ) (m : Fin 3 → ℕ)
  | keep
  | split (second : Bool) (left right : BranchTree)

/-- A closed rotation box `[a₁,b₁] × [a₂,b₂]`. -/
structure TBox where
  a1 : ℚ
  b1 : ℚ
  a2 : ℚ
  b2 : ℚ
  deriving DecidableEq, Repr

namespace TBox

def Contains (B : TBox) (t1 t2 : ℝ) : Prop :=
  (B.a1 : ℝ) ≤ t1 ∧ t1 ≤ B.b1 ∧ (B.a2 : ℝ) ≤ t2 ∧ t2 ≤ B.b2

def left (B : TBox) : Bool → TBox
  | false => ⟨B.a1, (B.a1 + B.b1) / 2, B.a2, B.b2⟩
  | true => ⟨B.a1, B.b1, B.a2, (B.a2 + B.b2) / 2⟩

def right (B : TBox) : Bool → TBox
  | false => ⟨(B.a1 + B.b1) / 2, B.b1, B.a2, B.b2⟩
  | true => ⟨B.a1, B.b1, (B.a2 + B.b2) / 2, B.b2⟩

def unit : TBox := ⟨0, 1, 0, 1⟩

theorem split_covers (B : TBox) (second : Bool) {t1 t2 : ℝ} (h : B.Contains t1 t2) :
    (B.left second).Contains t1 t2 ∨ (B.right second).Contains t1 t2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases second
  · by_cases hm : t1 ≤ ((B.a1 + B.b1) / 2 : ℚ)
    · exact Or.inl ⟨h1, hm, h3, h4⟩
    · exact Or.inr ⟨le_of_lt (lt_of_not_ge hm), h2, h3, h4⟩
  · by_cases hm : t2 ≤ ((B.a2 + B.b2) / 2 : ℚ)
    · exact Or.inl ⟨h1, h2, h3, hm⟩
    · exact Or.inr ⟨h1, h2, le_of_lt (lt_of_not_ge hm), h4⟩

/-- Boxes inside the unit square: `0 ≤ a` and `b ≤ 1` in both coordinates. -/
def Inside (B : TBox) : Prop := 0 ≤ B.a1 ∧ B.b1 ≤ 1 ∧ 0 ≤ B.a2 ∧ B.b2 ≤ 1

theorem left_inside {B : TBox} (hB : B.Inside) (second : Bool) {t1 t2 : ℝ}
    (h : (B.left second).Contains t1 t2) : (B.left second).Inside := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  obtain ⟨k1, k2, k3, k4⟩ := h
  cases second <;> simp only [left] at k1 k2 k3 k4 ⊢
  · have : (B.a1 : ℝ) ≤ ((B.a1 + B.b1) / 2 : ℚ) := k1.trans k2
    push_cast at this
    have hab : B.a1 ≤ B.b1 := by exact_mod_cast (by linarith : (B.a1 : ℝ) ≤ B.b1)
    exact ⟨h1, by linarith, h3, h4⟩
  · have : (B.a2 : ℝ) ≤ ((B.a2 + B.b2) / 2 : ℚ) := k3.trans k4
    push_cast at this
    have hab : B.a2 ≤ B.b2 := by exact_mod_cast (by linarith : (B.a2 : ℝ) ≤ B.b2)
    exact ⟨h1, h2, h3, by linarith⟩

theorem right_inside {B : TBox} (hB : B.Inside) (second : Bool) {t1 t2 : ℝ}
    (h : (B.right second).Contains t1 t2) : (B.right second).Inside := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  obtain ⟨k1, k2, k3, k4⟩ := h
  cases second <;> simp only [right] at k1 k2 k3 k4 ⊢
  · have : ((B.a1 + B.b1) / 2 : ℚ) ≤ (B.b1 : ℝ) := k1.trans k2
    push_cast at this
    have hab : B.a1 ≤ B.b1 := by exact_mod_cast (by linarith : (B.a1 : ℝ) ≤ B.b1)
    exact ⟨by linarith, h2, h3, h4⟩
  · have : ((B.a2 + B.b2) / 2 : ℚ) ≤ (B.b2 : ℝ) := k3.trans k4
    push_cast at this
    have hab : B.a2 ≤ B.b2 := by exact_mod_cast (by linarith : (B.a2 : ℝ) ≤ B.b2)
    exact ⟨h1, h2, by linarith, h4⟩

end TBox

namespace BranchTree

def check (code : ℕ) : BranchTree → TBox → Bool
  | .reject l m, B => (mkCert code l m).check (rotationBox B.a1 B.b1 B.a2 B.b2)
  | .keep, _ => true
  | .split second l r, B => l.check code (B.left second) && r.check code (B.right second)

def residuals : BranchTree → TBox → List TBox
  | .reject _ _, _ => []
  | .keep, B => [B]
  | .split second l r, B => l.residuals (B.left second) ++ r.residuals (B.right second)

def keptCount : BranchTree → ℕ
  | .reject _ _ => 0
  | .keep => 1
  | .split _ l r => l.keptCount + r.keptCount

def rejectCount : BranchTree → ℕ
  | .reject _ _ => 1
  | .keep => 0
  | .split _ l r => l.rejectCount + r.rejectCount

/-- A checked tree places every packing realizing its branch in a residual
box. -/
theorem check_sound (T : BranchTree) (code : ℕ) (B : TBox) (hB : B.Inside)
    (h : T.check code B = true) (P : SubcriticalRationalRotationPacking 3)
    (h0 : P.t 0 = 0) (hreal : Realizes P code) (ht : B.Contains (P.t 1) (P.t 2)) :
    ∃ R ∈ T.residuals B, R.Contains (P.t 1) (P.t 2) := by
  induction T generalizing B with
  | reject l m =>
    exfalso
    obtain ⟨h1, h2, h3, h4⟩ := hB
    exact cert_excludes (mkCert code l m) h P h0 hreal (by exact_mod_cast h1)
      ⟨ht.1, ht.2.1⟩ (by exact_mod_cast h2) (by exact_mod_cast h3) ⟨ht.2.2.1, ht.2.2.2⟩
      (by exact_mod_cast h4)
  | keep => exact ⟨B, by simp [residuals], ht⟩
  | split second l r hl hr =>
    simp only [check, Bool.and_eq_true] at h
    rcases B.split_covers second ht with hc | hc
    · obtain ⟨R, hR, hRc⟩ := hl (B.left second) (TBox.left_inside hB second hc) h.1 hc
      exact ⟨R, by simp [residuals, hR], hRc⟩
    · obtain ⟨R, hR, hRc⟩ := hr (B.right second) (TBox.right_inside hB second hc) h.2 hc
      exact ⟨R, by simp [residuals, hR], hRc⟩

end BranchTree

/-- A branch tree labelled by its branch code. -/
structure CodedTree where
  code : ℕ
  tree : BranchTree

/-- A family of checked trees covering all 512 branches over the unit rotation
square localizes every subcritical normalized packing in a residual box of the
tree of a branch it realizes. -/
theorem coded_trees_localize (L : List CodedTree)
    (hcodes : L.map CodedTree.code = List.range 512)
    (hcheck : ∀ T ∈ L, T.tree.check T.code TBox.unit = true)
    (P : SubcriticalRationalRotationPacking 3) (h0 : P.t 0 = 0) :
    ∃ T ∈ L, Realizes P T.code ∧
      ∃ R ∈ T.tree.residuals TBox.unit, R.Contains (P.t 1) (P.t 2) := by
  obtain ⟨code, hlt, hreal⟩ := exists_realized P h0
  have hmem : code ∈ L.map CodedTree.code := by rw [hcodes]; simpa using hlt
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hmem
  refine ⟨T, hT, hreal, T.tree.check_sound T.code TBox.unit ?_ (hcheck T hT) P h0 hreal ?_⟩
  · simp [TBox.Inside, TBox.unit]
  · exact ⟨by simpa [TBox.unit] using P.t_nonneg 1, by simpa [TBox.unit] using P.t_le_one 1,
      by simpa [TBox.unit] using P.t_nonneg 2, by simpa [TBox.unit] using P.t_le_one 2⟩

end

end CenterElimination
end ThreeSquares
