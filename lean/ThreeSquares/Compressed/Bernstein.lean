import ThreeSquares.Compressed.Bridge

/-! Shared degree-four Bernstein identity. Every specialized instance checks
only fifteen rational coefficient signs. The symbolic identity is proved once. -/
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace ThreeSquares.CenterElimination.Compressed
noncomputable section

def triangleCoefficients (n : Numerator) (T : Triangle) : Fin 15 → ℚ :=
  ![n 0 0 * (1) + n 0 1 * (T.ay) + n 0 2 * (T.ay ^ 2) + n 1 0 * (T.ax) + n 1 1 * (T.ax * T.ay) + n 1 2 * (T.ax * T.ay ^ 2) + n 2 0 * (T.ax ^ 2) + n 2 1 * (T.ax ^ 2 * T.ay) + n 2 2 * (T.ax ^ 2 * T.ay ^ 2),
    n 0 0 * (4) + n 0 1 * (T.cy + 3 * T.ay) + n 0 2 * (2 * T.ay * T.cy + 2 * T.ay ^ 2) + n 1 0 * (T.cx + 3 * T.ax) + n 1 1 * (T.ay * T.cx + T.ax * T.cy + 2 * T.ax * T.ay) + n 1 2 * (T.ay ^ 2 * T.cx + 2 * T.ax * T.ay * T.cy + T.ax * T.ay ^ 2) + n 2 0 * (2 * T.ax * T.cx + 2 * T.ax ^ 2) + n 2 1 * (2 * T.ax * T.ay * T.cx + T.ax ^ 2 * T.cy + T.ax ^ 2 * T.ay) + n 2 2 * (2 * T.ax * T.ay ^ 2 * T.cx + 2 * T.ax ^ 2 * T.ay * T.cy),
    n 0 0 * (6) + n 0 1 * (3 * T.cy + 3 * T.ay) + n 0 2 * (T.cy ^ 2 + 4 * T.ay * T.cy + T.ay ^ 2) + n 1 0 * (3 * T.cx + 3 * T.ax) + n 1 1 * (T.cx * T.cy + 2 * T.ay * T.cx + 2 * T.ax * T.cy + T.ax * T.ay) + n 1 2 * (2 * T.ay * T.cx * T.cy + T.ay ^ 2 * T.cx + T.ax * T.cy ^ 2 + 2 * T.ax * T.ay * T.cy) + n 2 0 * (T.cx ^ 2 + 4 * T.ax * T.cx + T.ax ^ 2) + n 2 1 * (T.ay * T.cx ^ 2 + 2 * T.ax * T.cx * T.cy + 2 * T.ax * T.ay * T.cx + T.ax ^ 2 * T.cy) + n 2 2 * (T.ay ^ 2 * T.cx ^ 2 + 4 * T.ax * T.ay * T.cx * T.cy + T.ax ^ 2 * T.cy ^ 2),
    n 0 0 * (4) + n 0 1 * (3 * T.cy + T.ay) + n 0 2 * (2 * T.cy ^ 2 + 2 * T.ay * T.cy) + n 1 0 * (3 * T.cx + T.ax) + n 1 1 * (2 * T.cx * T.cy + T.ay * T.cx + T.ax * T.cy) + n 1 2 * (T.cx * T.cy ^ 2 + 2 * T.ay * T.cx * T.cy + T.ax * T.cy ^ 2) + n 2 0 * (2 * T.cx ^ 2 + 2 * T.ax * T.cx) + n 2 1 * (T.cx ^ 2 * T.cy + T.ay * T.cx ^ 2 + 2 * T.ax * T.cx * T.cy) + n 2 2 * (2 * T.ay * T.cx ^ 2 * T.cy + 2 * T.ax * T.cx * T.cy ^ 2),
    n 0 0 * (1) + n 0 1 * (T.cy) + n 0 2 * (T.cy ^ 2) + n 1 0 * (T.cx) + n 1 1 * (T.cx * T.cy) + n 1 2 * (T.cx * T.cy ^ 2) + n 2 0 * (T.cx ^ 2) + n 2 1 * (T.cx ^ 2 * T.cy) + n 2 2 * (T.cx ^ 2 * T.cy ^ 2),
    n 0 0 * (4) + n 0 1 * (T.by_ + 3 * T.ay) + n 0 2 * (2 * T.ay * T.by_ + 2 * T.ay ^ 2) + n 1 0 * (T.bx + 3 * T.ax) + n 1 1 * (T.ay * T.bx + T.ax * T.by_ + 2 * T.ax * T.ay) + n 1 2 * (T.ay ^ 2 * T.bx + 2 * T.ax * T.ay * T.by_ + T.ax * T.ay ^ 2) + n 2 0 * (2 * T.ax * T.bx + 2 * T.ax ^ 2) + n 2 1 * (2 * T.ax * T.ay * T.bx + T.ax ^ 2 * T.by_ + T.ax ^ 2 * T.ay) + n 2 2 * (2 * T.ax * T.ay ^ 2 * T.bx + 2 * T.ax ^ 2 * T.ay * T.by_),
    n 0 0 * (12) + n 0 1 * (3 * T.cy + 3 * T.by_ + 6 * T.ay) + n 0 2 * (2 * T.by_ * T.cy + 4 * T.ay * T.cy + 4 * T.ay * T.by_ + 2 * T.ay ^ 2) + n 1 0 * (3 * T.cx + 3 * T.bx + 6 * T.ax) + n 1 1 * (T.by_ * T.cx + T.bx * T.cy + 2 * T.ay * T.cx + 2 * T.ay * T.bx + 2 * T.ax * T.cy + 2 * T.ax * T.by_ + 2 * T.ax * T.ay) + n 1 2 * (2 * T.ay * T.by_ * T.cx + 2 * T.ay * T.bx * T.cy + T.ay ^ 2 * T.cx + T.ay ^ 2 * T.bx + 2 * T.ax * T.by_ * T.cy + 2 * T.ax * T.ay * T.cy + 2 * T.ax * T.ay * T.by_) + n 2 0 * (2 * T.bx * T.cx + 4 * T.ax * T.cx + 4 * T.ax * T.bx + 2 * T.ax ^ 2) + n 2 1 * (2 * T.ay * T.bx * T.cx + 2 * T.ax * T.by_ * T.cx + 2 * T.ax * T.bx * T.cy + 2 * T.ax * T.ay * T.cx + 2 * T.ax * T.ay * T.bx + T.ax ^ 2 * T.cy + T.ax ^ 2 * T.by_) + n 2 2 * (2 * T.ay ^ 2 * T.bx * T.cx + 4 * T.ax * T.ay * T.by_ * T.cx + 4 * T.ax * T.ay * T.bx * T.cy + 2 * T.ax ^ 2 * T.by_ * T.cy),
    n 0 0 * (12) + n 0 1 * (6 * T.cy + 3 * T.by_ + 3 * T.ay) + n 0 2 * (2 * T.cy ^ 2 + 4 * T.by_ * T.cy + 4 * T.ay * T.cy + 2 * T.ay * T.by_) + n 1 0 * (6 * T.cx + 3 * T.bx + 3 * T.ax) + n 1 1 * (2 * T.cx * T.cy + 2 * T.by_ * T.cx + 2 * T.bx * T.cy + 2 * T.ay * T.cx + T.ay * T.bx + 2 * T.ax * T.cy + T.ax * T.by_) + n 1 2 * (2 * T.by_ * T.cx * T.cy + T.bx * T.cy ^ 2 + 2 * T.ay * T.cx * T.cy + 2 * T.ay * T.by_ * T.cx + 2 * T.ay * T.bx * T.cy + T.ax * T.cy ^ 2 + 2 * T.ax * T.by_ * T.cy) + n 2 0 * (2 * T.cx ^ 2 + 4 * T.bx * T.cx + 4 * T.ax * T.cx + 2 * T.ax * T.bx) + n 2 1 * (T.by_ * T.cx ^ 2 + 2 * T.bx * T.cx * T.cy + T.ay * T.cx ^ 2 + 2 * T.ay * T.bx * T.cx + 2 * T.ax * T.cx * T.cy + 2 * T.ax * T.by_ * T.cx + 2 * T.ax * T.bx * T.cy) + n 2 2 * (2 * T.ay * T.by_ * T.cx ^ 2 + 4 * T.ay * T.bx * T.cx * T.cy + 4 * T.ax * T.by_ * T.cx * T.cy + 2 * T.ax * T.bx * T.cy ^ 2),
    n 0 0 * (4) + n 0 1 * (3 * T.cy + T.by_) + n 0 2 * (2 * T.cy ^ 2 + 2 * T.by_ * T.cy) + n 1 0 * (3 * T.cx + T.bx) + n 1 1 * (2 * T.cx * T.cy + T.by_ * T.cx + T.bx * T.cy) + n 1 2 * (T.cx * T.cy ^ 2 + 2 * T.by_ * T.cx * T.cy + T.bx * T.cy ^ 2) + n 2 0 * (2 * T.cx ^ 2 + 2 * T.bx * T.cx) + n 2 1 * (T.cx ^ 2 * T.cy + T.by_ * T.cx ^ 2 + 2 * T.bx * T.cx * T.cy) + n 2 2 * (2 * T.by_ * T.cx ^ 2 * T.cy + 2 * T.bx * T.cx * T.cy ^ 2),
    n 0 0 * (6) + n 0 1 * (3 * T.by_ + 3 * T.ay) + n 0 2 * (T.by_ ^ 2 + 4 * T.ay * T.by_ + T.ay ^ 2) + n 1 0 * (3 * T.bx + 3 * T.ax) + n 1 1 * (T.bx * T.by_ + 2 * T.ay * T.bx + 2 * T.ax * T.by_ + T.ax * T.ay) + n 1 2 * (2 * T.ay * T.bx * T.by_ + T.ay ^ 2 * T.bx + T.ax * T.by_ ^ 2 + 2 * T.ax * T.ay * T.by_) + n 2 0 * (T.bx ^ 2 + 4 * T.ax * T.bx + T.ax ^ 2) + n 2 1 * (T.ay * T.bx ^ 2 + 2 * T.ax * T.bx * T.by_ + 2 * T.ax * T.ay * T.bx + T.ax ^ 2 * T.by_) + n 2 2 * (T.ay ^ 2 * T.bx ^ 2 + 4 * T.ax * T.ay * T.bx * T.by_ + T.ax ^ 2 * T.by_ ^ 2),
    n 0 0 * (12) + n 0 1 * (3 * T.cy + 6 * T.by_ + 3 * T.ay) + n 0 2 * (4 * T.by_ * T.cy + 2 * T.by_ ^ 2 + 2 * T.ay * T.cy + 4 * T.ay * T.by_) + n 1 0 * (3 * T.cx + 6 * T.bx + 3 * T.ax) + n 1 1 * (2 * T.by_ * T.cx + 2 * T.bx * T.cy + 2 * T.bx * T.by_ + T.ay * T.cx + 2 * T.ay * T.bx + T.ax * T.cy + 2 * T.ax * T.by_) + n 1 2 * (T.by_ ^ 2 * T.cx + 2 * T.bx * T.by_ * T.cy + 2 * T.ay * T.by_ * T.cx + 2 * T.ay * T.bx * T.cy + 2 * T.ay * T.bx * T.by_ + 2 * T.ax * T.by_ * T.cy + T.ax * T.by_ ^ 2) + n 2 0 * (4 * T.bx * T.cx + 2 * T.bx ^ 2 + 2 * T.ax * T.cx + 4 * T.ax * T.bx) + n 2 1 * (2 * T.bx * T.by_ * T.cx + T.bx ^ 2 * T.cy + 2 * T.ay * T.bx * T.cx + T.ay * T.bx ^ 2 + 2 * T.ax * T.by_ * T.cx + 2 * T.ax * T.bx * T.cy + 2 * T.ax * T.bx * T.by_) + n 2 2 * (4 * T.ay * T.bx * T.by_ * T.cx + 2 * T.ay * T.bx ^ 2 * T.cy + 2 * T.ax * T.by_ ^ 2 * T.cx + 4 * T.ax * T.bx * T.by_ * T.cy),
    n 0 0 * (6) + n 0 1 * (3 * T.cy + 3 * T.by_) + n 0 2 * (T.cy ^ 2 + 4 * T.by_ * T.cy + T.by_ ^ 2) + n 1 0 * (3 * T.cx + 3 * T.bx) + n 1 1 * (T.cx * T.cy + 2 * T.by_ * T.cx + 2 * T.bx * T.cy + T.bx * T.by_) + n 1 2 * (2 * T.by_ * T.cx * T.cy + T.by_ ^ 2 * T.cx + T.bx * T.cy ^ 2 + 2 * T.bx * T.by_ * T.cy) + n 2 0 * (T.cx ^ 2 + 4 * T.bx * T.cx + T.bx ^ 2) + n 2 1 * (T.by_ * T.cx ^ 2 + 2 * T.bx * T.cx * T.cy + 2 * T.bx * T.by_ * T.cx + T.bx ^ 2 * T.cy) + n 2 2 * (T.by_ ^ 2 * T.cx ^ 2 + 4 * T.bx * T.by_ * T.cx * T.cy + T.bx ^ 2 * T.cy ^ 2),
    n 0 0 * (4) + n 0 1 * (3 * T.by_ + T.ay) + n 0 2 * (2 * T.by_ ^ 2 + 2 * T.ay * T.by_) + n 1 0 * (3 * T.bx + T.ax) + n 1 1 * (2 * T.bx * T.by_ + T.ay * T.bx + T.ax * T.by_) + n 1 2 * (T.bx * T.by_ ^ 2 + 2 * T.ay * T.bx * T.by_ + T.ax * T.by_ ^ 2) + n 2 0 * (2 * T.bx ^ 2 + 2 * T.ax * T.bx) + n 2 1 * (T.bx ^ 2 * T.by_ + T.ay * T.bx ^ 2 + 2 * T.ax * T.bx * T.by_) + n 2 2 * (2 * T.ay * T.bx ^ 2 * T.by_ + 2 * T.ax * T.bx * T.by_ ^ 2),
    n 0 0 * (4) + n 0 1 * (T.cy + 3 * T.by_) + n 0 2 * (2 * T.by_ * T.cy + 2 * T.by_ ^ 2) + n 1 0 * (T.cx + 3 * T.bx) + n 1 1 * (T.by_ * T.cx + T.bx * T.cy + 2 * T.bx * T.by_) + n 1 2 * (T.by_ ^ 2 * T.cx + 2 * T.bx * T.by_ * T.cy + T.bx * T.by_ ^ 2) + n 2 0 * (2 * T.bx * T.cx + 2 * T.bx ^ 2) + n 2 1 * (2 * T.bx * T.by_ * T.cx + T.bx ^ 2 * T.cy + T.bx ^ 2 * T.by_) + n 2 2 * (2 * T.bx * T.by_ ^ 2 * T.cx + 2 * T.bx ^ 2 * T.by_ * T.cy),
    n 0 0 * (1) + n 0 1 * (T.by_) + n 0 2 * (T.by_ ^ 2) + n 1 0 * (T.bx) + n 1 1 * (T.bx * T.by_) + n 1 2 * (T.bx * T.by_ ^ 2) + n 2 0 * (T.bx ^ 2) + n 2 1 * (T.bx ^ 2 * T.by_) + n 2 2 * (T.bx ^ 2 * T.by_ ^ 2)]

def bernsteinEval (b : Fin 15 → ℚ) (u v : ℝ) : ℝ :=
  (b 0 : ℝ) * (u ^ 0 * v ^ 0 * (1-u-v) ^ 4) +
    (b 1 : ℝ) * (u ^ 0 * v ^ 1 * (1-u-v) ^ 3) +
    (b 2 : ℝ) * (u ^ 0 * v ^ 2 * (1-u-v) ^ 2) +
    (b 3 : ℝ) * (u ^ 0 * v ^ 3 * (1-u-v) ^ 1) +
    (b 4 : ℝ) * (u ^ 0 * v ^ 4 * (1-u-v) ^ 0) +
    (b 5 : ℝ) * (u ^ 1 * v ^ 0 * (1-u-v) ^ 3) +
    (b 6 : ℝ) * (u ^ 1 * v ^ 1 * (1-u-v) ^ 2) +
    (b 7 : ℝ) * (u ^ 1 * v ^ 2 * (1-u-v) ^ 1) +
    (b 8 : ℝ) * (u ^ 1 * v ^ 3 * (1-u-v) ^ 0) +
    (b 9 : ℝ) * (u ^ 2 * v ^ 0 * (1-u-v) ^ 2) +
    (b 10 : ℝ) * (u ^ 2 * v ^ 1 * (1-u-v) ^ 1) +
    (b 11 : ℝ) * (u ^ 2 * v ^ 2 * (1-u-v) ^ 0) +
    (b 12 : ℝ) * (u ^ 3 * v ^ 0 * (1-u-v) ^ 1) +
    (b 13 : ℝ) * (u ^ 3 * v ^ 1 * (1-u-v) ^ 0) +
    (b 14 : ℝ) * (u ^ 4 * v ^ 0 * (1-u-v) ^ 0)

theorem triangleCoefficients_identity (n : Numerator) (T : Triangle) (u v : ℝ) :
    numEval n (T.x u v) (T.y u v) = bernsteinEval (triangleCoefficients n T) u v := by
  simp [numEval, Fin.sum_univ_three, Triangle.x, Triangle.y,
    triangleCoefficients, bernsteinEval]
  ring

theorem bernsteinEval_nonneg (b : Fin 15 → ℚ) (hb : ∀ i, 0 ≤ b i)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : u + v ≤ 1) :
    0 ≤ bernsteinEval b u v := by
  have hw : 0 ≤ 1-u-v := by linarith
  have h (i : Fin 15) : (0 : ℝ) ≤ b i := by exact_mod_cast hb i
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  have h8 := h 8
  have h9 := h 9
  have h10 := h 10
  have h11 := h 11
  have h12 := h 12
  have h13 := h 13
  have h14 := h 14
  unfold bernsteinEval
  positivity

theorem triangle_nonnegative_of_coefficients (n : Numerator) (T : Triangle)
    (h : ∀ i, 0 ≤ triangleCoefficients n T i)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : u + v ≤ 1) :
    0 ≤ numEval n (T.x u v) (T.y u v) := by
  rw [triangleCoefficients_identity]
  exact bernsteinEval_nonneg _ h u v hu hv hs

#print axioms triangle_nonnegative_of_coefficients
end
end ThreeSquares.CenterElimination.Compressed
