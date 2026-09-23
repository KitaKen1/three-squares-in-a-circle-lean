import ThreeSquares.StrictBound
import ThreeSquares.QuadFast

/-! Exact coefficient and domain interfaces for compressed certificates.
The generator supplies rational data; every coefficient identity and every
domain cover must be proved in Lean before it can exclude a packing. -/

set_option Elab.async false

noncomputable section
namespace ThreeSquares.CenterElimination.Compressed

abbrev Seven := Fin 7 → ℚ
abbrev Numerator := Fin 3 → Fin 3 → ℚ

def sevenEval (a : Seven) (x : Fin 4 → ℝ) : ℝ :=
  a 0 + a 1 * x 0 + a 2 * x 1 + a 3 * x 2 + a 4 * x 3 +
    a 5 * (x 0 * x 2 + x 1 * x 3) + a 6 * (x 0 * x 3 - x 1 * x 2)

def quadSignature (q : Quad) : Fin 13 → ℚ :=
  ![q.c + q.m 0 0 + q.m 2 2, q.v 0, q.v 1, q.v 2, q.v 3,
    q.m 1 1 - q.m 0 0, q.m 3 3 - q.m 2 2,
    q.m 0 1 + q.m 1 0, q.m 2 3 + q.m 3 2,
    q.m 0 2 + q.m 2 0, q.m 1 3 + q.m 3 1,
    q.m 0 3 + q.m 3 0, q.m 1 2 + q.m 2 1]

def sevenSignature (a : Seven) : Fin 13 → ℚ :=
  ![a 0, a 1, a 2, a 3, a 4, 0, 0, 0, 0, a 5, a 5, a 6, -a 6]

def quadMatches (q : Quad) (a : Seven) : Bool :=
  decide (∀ i, quadSignature q i = sevenSignature a i)

theorem matches_sound (q : Quad) (a : Seven) (h : quadMatches q a = true)
    (x : Fin 4 → ℝ) (hu : x 0 ^ 2 + x 1 ^ 2 = 1)
    (hv : x 2 ^ 2 + x 3 ^ 2 = 1) : q.eval x = sevenEval a x := by
  have hh : ∀ i, quadSignature q i = sevenSignature a i := of_decide_eq_true h
  have hr (i : Fin 13) : (quadSignature q i : ℝ) = (sevenSignature a i : ℝ) := by
    exact_mod_cast hh i
  have h0 := hr 0; have h1 := hr 1; have h2 := hr 2; have h3 := hr 3
  have h4 := hr 4; have h5 := hr 5; have h6 := hr 6; have h7 := hr 7
  have h8 := hr 8; have h9 := hr 9; have h10 := hr 10; have h11 := hr 11
  have h12 := hr 12
  dsimp [quadSignature, sevenSignature] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp only [Quad.eval, sevenEval, Fin.sum_univ_four]
  linear_combination h0 + x 0 * h1 + x 1 * h2 + x 2 * h3 + x 3 * h4 +
    x 1 ^ 2 * h5 + x 3 ^ 2 * h6 + x 0 * x 1 * h7 + x 2 * x 3 * h8 +
    x 0 * x 2 * h9 + x 1 * x 3 * h10 + x 0 * x 3 * h11 + x 1 * x 2 * h12 +
    (q.m 0 0 : ℝ) * hu + (q.m 2 2 : ℝ) * hv

def numerator (a : Seven) : Numerator :=
  let k := a 0 - 425 / 256
  ![![k + a 1 + a 3 + a 5, 2 * a 4 + 2 * a 6, k + a 1 - a 3 - a 5],
    ![2 * a 2 - 2 * a 6, 4 * a 5, 2 * a 2 + 2 * a 6],
    ![k - a 1 + a 3 - a 5, 2 * a 4 - 2 * a 6, k - a 1 - a 3 + a 5]]

def numEval (n : Numerator) (s t : ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, (n i j : ℝ) * s ^ i.val * t ^ j.val

theorem numEval_scale (d : ℚ) (n : Numerator) (s t : ℝ) :
    numEval (fun i j => d * n i j) s t = (d : ℝ) * numEval n s t := by
  simp only [numEval, Fin.sum_univ_three]
  push_cast
  ring

theorem numerator_identity (a : Seven) (s t : ℝ) :
    numEval (numerator a) s t = (1 + s ^ 2) * (1 + t ^ 2) *
      (sevenEval a (rotationVector s t) - 425 / 256) := by
  have hs : (1 + s ^ 2) ≠ 0 := ne_of_gt (by positivity)
  have ht : (1 + t ^ 2) ≠ 0 := ne_of_gt (by positivity)
  simp [numEval, numerator, sevenEval, rotationVector, rationalCos, rationalSin,
    Fin.sum_univ_three]
  field_simp
  ring

theorem seven_lower_of_num_nonneg (a : Seven) {s t : ℝ}
    (h : 0 ≤ numEval (numerator a) s t) :
    (425 / 256 : ℝ) ≤ sevenEval a (rotationVector s t) := by
  rw [numerator_identity] at h
  have hp : 0 < (1 + s ^ 2) * (1 + t ^ 2) := by positivity
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hp).mp h)

/-- This is the connection to actual subcritical FC packings. -/
theorem certificate_excludes (C : Certificate) (a : Seven) (σ : Fin 3 → ℚ)
    (hw : C.wellFormed = true)
    (hσ : ∀ e, σ e = 1 ∨ σ e = -1 ∨ σ e = 0)
    (hmatch : quadMatches (C.lowerQuad σ) a = true)
    (P : SubcriticalRationalRotationPacking 3) (h0 : P.t 0 = 0)
    (hreal : Realizes P C.code)
    (hn : 0 ≤ numEval (numerator a) (P.t 1) (P.t 2)) : False := by
  have hstrict := C.lowerBound_lt_of_realizes hw P h0 hreal
  have hle := lowerQuad_le C hw (rotationVector (P.t 1) (P.t 2)) σ hσ
  have heq := matches_sound (C.lowerQuad σ) a hmatch (rotationVector (P.t 1) (P.t 2))
    (by simpa [rotationVector] using rational_rotation_unit (P.t 1))
    (by simpa [rotationVector] using rational_rotation_unit (P.t 2))
  rw [heq] at hle
  exact (not_lt_of_ge ((seven_lower_of_num_nonneg a hn).trans hle)) hstrict

structure Triangle where
  ax : ℚ
  ay : ℚ
  bx : ℚ
  by_ : ℚ
  cx : ℚ
  cy : ℚ

def Triangle.x (T : Triangle) (u v : ℝ) : ℝ :=
  T.ax + (T.bx - T.ax : ℚ) * u + (T.cx - T.ax : ℚ) * v
def Triangle.y (T : Triangle) (u v : ℝ) : ℝ :=
  T.ay + (T.by_ - T.ay : ℚ) * u + (T.cy - T.ay : ℚ) * v
def Triangle.det (T : Triangle) : ℚ :=
  (T.bx - T.ax) * (T.cy - T.ay) - (T.cx - T.ax) * (T.by_ - T.ay)
def Triangle.u (T : Triangle) (x y : ℝ) : ℝ :=
  ((x - T.ax) * (T.cy - T.ay : ℚ) - (y - T.ay) * (T.cx - T.ax : ℚ)) / T.det
def Triangle.v (T : Triangle) (x y : ℝ) : ℝ :=
  ((y - T.ay) * (T.bx - T.ax : ℚ) - (x - T.ax) * (T.by_ - T.ay : ℚ)) / T.det
def Triangle.Contains (T : Triangle) (x y : ℝ) : Prop :=
  0 ≤ T.u x y ∧ 0 ≤ T.v x y ∧ T.u x y + T.v x y ≤ 1

theorem Triangle.reconstruct (T : Triangle) (hT : T.det ≠ 0) (x y : ℝ) :
    T.x (T.u x y) (T.v x y) = x ∧ T.y (T.u x y) (T.v x y) = y := by
  have hd : (T.det : ℝ) ≠ 0 := by exact_mod_cast hT
  constructor <;> simp only [Triangle.x, Triangle.y, Triangle.u, Triangle.v]
    <;> field_simp
    <;> simp only [Triangle.det] at *
    <;> push_cast at *
    <;> ring

theorem Triangle.nonneg (T : Triangle) (hT : T.det ≠ 0) (n : Numerator)
    (h : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u + v ≤ 1 → 0 ≤ numEval n (T.x u v) (T.y u v))
    {x y : ℝ} (hxy : T.Contains x y) : 0 ≤ numEval n x y := by
  have hr := T.reconstruct hT x y
  simpa only [hr.1, hr.2] using h (T.u x y) (T.v x y) hxy.1 hxy.2.1 hxy.2.2

#print axioms certificate_excludes
#print axioms Triangle.nonneg
end ThreeSquares.CenterElimination.Compressed
