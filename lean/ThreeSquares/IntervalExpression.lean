import ThreeSquares.RationalInterval

/-! # Polynomial and absolute-value constraints with verified enclosures

The expression language suffices for the finite square-packing model: rational
constants, addition, negation, multiplication, squares and absolute values.
Division by a nonzero rational is multiplication by its rational reciprocal.
-/

namespace ThreeSquares

abbrev RationalBox (n : ℕ) := Fin n → RationalInterval

def RationalBox.Contains {n : ℕ} (B : RationalBox n) (x : Fin n → ℝ) : Prop :=
  ∀ i, (B i).Contains (x i)

inductive IntervalExpr (n : ℕ) where
  | const : ℚ → IntervalExpr n
  | var : Fin n → IntervalExpr n
  | add : IntervalExpr n → IntervalExpr n → IntervalExpr n
  | neg : IntervalExpr n → IntervalExpr n
  | mul : IntervalExpr n → IntervalExpr n → IntervalExpr n
  | square : IntervalExpr n → IntervalExpr n
  | abs : IntervalExpr n → IntervalExpr n
  deriving Repr, DecidableEq

namespace IntervalExpr

noncomputable def eval {n : ℕ} (x : Fin n → ℝ) : IntervalExpr n → ℝ
  | .const q => q
  | .var i => x i
  | .add e f => e.eval x + f.eval x
  | .neg e => -e.eval x
  | .mul e f => e.eval x * f.eval x
  | .square e => (e.eval x) ^ 2
  | .abs e => |e.eval x|

def enclose {n : ℕ} (B : RationalBox n) : IntervalExpr n → RationalInterval
  | .const q => .singleton q
  | .var i => B i
  | .add e f => (e.enclose B).add (f.enclose B)
  | .neg e => (e.enclose B).neg
  | .mul e f => (e.enclose B).mul (f.enclose B)
  | .square e => (e.enclose B).square
  | .abs e => (e.enclose B).abs

theorem enclose_contains {n : ℕ} (e : IntervalExpr n) {B : RationalBox n}
    {x : Fin n → ℝ} (hx : B.Contains x) : (e.enclose B).Contains (e.eval x) := by
  induction e with
  | const q => exact RationalInterval.singleton_contains q
  | var i => exact hx i
  | add e f he hf => exact RationalInterval.add_contains he hf
  | neg e he => exact RationalInterval.neg_contains he
  | mul e f he hf => exact RationalInterval.mul_contains he hf
  | square e he => exact RationalInterval.square_contains he
  | abs e he => exact RationalInterval.abs_contains he

end IntervalExpr

inductive IntervalFormula (n : ℕ) where
  | nonpos : IntervalExpr n → IntervalFormula n
  | negative : IntervalExpr n → IntervalFormula n
  | zero : IntervalExpr n → IntervalFormula n
  | conj : IntervalFormula n → IntervalFormula n → IntervalFormula n
  | disj : IntervalFormula n → IntervalFormula n → IntervalFormula n
  deriving Repr, DecidableEq

namespace IntervalFormula

def Holds {n : ℕ} (x : Fin n → ℝ) : IntervalFormula n → Prop
  | .nonpos e => e.eval x ≤ 0
  | .negative e => e.eval x < 0
  | .zero e => e.eval x = 0
  | .conj p q => p.Holds x ∧ q.Holds x
  | .disj p q => p.Holds x ∨ q.Holds x

/-- `true` certifies impossibility. `false` makes no claim of feasibility. -/
def refute {n : ℕ} (B : RationalBox n) : IntervalFormula n → Bool
  | .nonpos e => decide (0 < (e.enclose B).lo)
  | .negative e => decide (0 ≤ (e.enclose B).lo)
  | .zero e => decide (0 < (e.enclose B).lo) || decide ((e.enclose B).hi < 0)
  | .conj p q => p.refute B || q.refute B
  | .disj p q => p.refute B && q.refute B

theorem refute_sound {n : ℕ} (p : IntervalFormula n) {B : RationalBox n}
    {x : Fin n → ℝ} (hx : B.Contains x) (h : p.refute B = true) : ¬ p.Holds x := by
  induction p with
  | nonpos e =>
    have hb := e.enclose_contains hx
    have hr : 0 < (e.enclose B).lo := by simpa [refute] using h
    have hr' : (0 : ℝ) < (e.enclose B).lo := by exact_mod_cast hr
    intro hp
    exact (not_le_of_gt (hr'.trans_le hb.1)) hp
  | negative e =>
    have hb := e.enclose_contains hx
    have hr : 0 ≤ (e.enclose B).lo := by simpa [refute] using h
    have hr' : (0 : ℝ) ≤ (e.enclose B).lo := by exact_mod_cast hr
    intro hp
    exact (not_lt_of_ge (hr'.trans hb.1)) hp
  | zero e =>
    have hb := e.enclose_contains hx
    have hr : 0 < (e.enclose B).lo ∨ (e.enclose B).hi < 0 := by simpa [refute] using h
    intro hp
    change e.eval x = 0 at hp
    rcases hr with hr | hr
    · have hr' : (0 : ℝ) < (e.enclose B).lo := by exact_mod_cast hr
      linarith [hb.1]
    · have hr' : (e.enclose B).hi < (0 : ℝ) := by exact_mod_cast hr
      linarith [hb.2]
  | conj p q hp hq =>
    have hr : p.refute B = true ∨ q.refute B = true := by simpa [refute] using h
    rintro ⟨hp', hq'⟩
    rcases hr with h | h
    · exact hp h hp'
    · exact hq h hq'
  | disj p q hp hq =>
    have hr : p.refute B = true ∧ q.refute B = true := by simpa [refute] using h
    intro hor
    rcases hor with h | h
    · exact hp hr.1 h
    · exact hq hr.2 h

end IntervalFormula
end ThreeSquares
