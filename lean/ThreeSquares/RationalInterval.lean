import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! # Exact rational interval arithmetic

Endpoints are rational numbers and every computation is executable. Empty
intervals are permitted; soundness only assumes that the input contains the
real value in question. No floating-point operations or external oracle occur.
-/

namespace ThreeSquares

structure RationalInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

namespace RationalInterval

def Contains (I : RationalInterval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ I.hi

def singleton (q : ℚ) : RationalInterval := ⟨q, q⟩
def add (I J : RationalInterval) : RationalInterval := ⟨I.lo + J.lo, I.hi + J.hi⟩
def neg (I : RationalInterval) : RationalInterval := ⟨-I.hi, -I.lo⟩
def mul (I J : RationalInterval) : RationalInterval :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩
def abs (I : RationalInterval) : RationalInterval :=
  ⟨max 0 (max I.lo (-I.hi)), max |I.lo| |I.hi|⟩
def square (I : RationalInterval) : RationalInterval := ⟨I.abs.lo ^ 2, I.abs.hi ^ 2⟩

theorem singleton_contains (q : ℚ) : (singleton q).Contains q := ⟨le_rfl, le_rfl⟩

theorem add_contains {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.add J).Contains (x + y) := by
  simp only [Contains, add, Rat.cast_add] at *
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem neg_contains {I : RationalInterval} {x : ℝ}
    (hx : I.Contains x) : I.neg.Contains (-x) := by
  simp only [Contains, neg, Rat.cast_neg] at *
  exact ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

private theorem scalar_bounds {a b x : ℝ} (c : ℝ) (hx : a ≤ x ∧ x ≤ b) :
    min (c * a) (c * b) ≤ c * x ∧ c * x ≤ max (c * a) (c * b) := by
  by_cases hc : 0 ≤ c
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hx.1 hc),
      (mul_le_mul_of_nonneg_left hx.2 hc).trans (le_max_right _ _)⟩
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hx.2 hc'),
      (mul_le_mul_of_nonpos_left hx.1 hc').trans (le_max_left _ _)⟩

theorem mul_contains {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.mul J).Contains (x * y) := by
  have ha := scalar_bounds (I.lo : ℝ) hy
  have hb := scalar_bounds (I.hi : ℝ) hy
  have hxy := scalar_bounds y hx
  rw [mul_comm y x, mul_comm y (I.lo : ℝ), mul_comm y (I.hi : ℝ)] at hxy
  simp only [Contains, mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  constructor
  · exact (min_le_min ha.1 hb.1).trans hxy.1
  · exact hxy.2.trans (max_le_max ha.2 hb.2)

theorem abs_contains {I : RationalInterval} {x : ℝ}
    (hx : I.Contains x) : I.abs.Contains |x| := by
  simp only [Contains, abs, Rat.cast_max, Rat.cast_zero, Rat.cast_neg, Rat.cast_abs]
  constructor
  · exact max_le (abs_nonneg x) (max_le (hx.1.trans (le_abs_self x))
      ((neg_le_neg hx.2).trans (neg_le_abs x)))
  · apply abs_le.mpr
    constructor
    · have h : -(I.lo : ℝ) ≤ max |(I.lo : ℝ)| |(I.hi : ℝ)| :=
        (neg_le_abs (I.lo : ℝ)).trans (le_max_left _ _)
      linarith [hx.1]
    · exact hx.2.trans ((le_abs_self _).trans (le_max_right _ _))

theorem square_contains {I : RationalInterval} {x : ℝ}
    (hx : I.Contains x) : I.square.Contains (x ^ 2) := by
  have h := abs_contains hx
  have hl : 0 ≤ (I.abs.lo : ℝ) := by
    simp only [abs, Rat.cast_max, Rat.cast_zero, Rat.cast_neg]
    exact le_max_left _ _
  simp only [Contains, square, Rat.cast_pow]
  have habs := abs_nonneg x
  have heq : |x| ^ 2 = x ^ 2 := sq_abs x
  constructor <;> nlinarith only [h.1, h.2, hl, habs, heq]

theorem not_contains_of_empty {I : RationalInterval} (h : I.hi < I.lo) (x : ℝ) :
    ¬ I.Contains x := by
  have h' : (I.hi : ℝ) < I.lo := by exact_mod_cast h
  intro hx
  exact (not_le_of_gt h') (hx.1.trans hx.2)

end RationalInterval
end ThreeSquares
