import ThreeSquares.FCDefinitions
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # An explicit packing of three unit squares at radius `5 * sqrt 17 / 16`

Every theorem in this file is unconditional. The packing consists of three
translations of the open unit square, using the exact FC definitions.
-/

open scoped NNReal
open SquarePacking

noncomputable section

namespace ThreeSquares

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def radius : ℝ≥0 := (5 * NNReal.sqrt 17) / 16

theorem radius_sq : radius ^ 2 = (425 / 256 : ℝ≥0) := by
  norm_num [radius, div_pow, mul_pow, NNReal.sq_sqrt]

theorem radius_sq_real : (radius : ℝ) ^ 2 = 425 / 256 := by
  rw [← NNReal.coe_pow, radius_sq]
  norm_num

theorem radius_pos : 0 < radius := by
  unfold radius
  positivity

def point (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]

@[simp] theorem point_zero (x y : ℝ) : point x y 0 = x := rfl
@[simp] theorem point_one (x y : ℝ) : point x y 1 = y := rfl

/-- Lower-left corners of the three translated open unit squares. -/
def offset : Fin 3 → Plane :=
  ![point (-19 / 16) (-1 / 2), point (-3 / 16) (-1), point (-3 / 16) 0]

noncomputable def embedding (i : Fin 3) : Plane ≃ᵢ Plane :=
  IsometryEquiv.vaddConst (offset i)

@[simp] theorem embedding_apply (i : Fin 3) (p : Plane) (k : Fin 2) :
    embedding i p k = p k + offset i k := rfl

private theorem square_lt_of_bounds {x a : ℝ} (hlo : -a < x) (hhi : x < a) :
    x ^ 2 < a ^ 2 := by
  nlinarith [mul_pos (sub_pos.mpr hhi) (sub_pos.mpr hlo)]

theorem embedding_inside (i : Fin 3) :
    embedding i '' UnitSquare ⊆ Circle radius := by
  rintro _ ⟨p, hp, rfl⟩
  rcases hp with ⟨hx0, hx1, hy0, hy1⟩
  change (embedding i p 0) ^ 2 + (embedding i p 1) ^ 2 < (radius : ℝ) ^ 2
  rw [radius_sq_real]
  fin_cases i
  · change (p 0 + -19 / 16) ^ 2 + (p 1 + -1 / 2) ^ 2 < 425 / 256
    have hx := square_lt_of_bounds (x := p 0 + -19 / 16) (a := 19 / 16)
      (by linarith) (by linarith)
    have hy := square_lt_of_bounds (x := p 1 + -1 / 2) (a := 1 / 2)
      (by linarith) (by linarith)
    nlinarith
  · change (p 0 + -3 / 16) ^ 2 + (p 1 + -1) ^ 2 < 425 / 256
    have hx := square_lt_of_bounds (x := p 0 + -3 / 16) (a := 13 / 16)
      (by linarith) (by linarith)
    have hy := square_lt_of_bounds (x := p 1 + -1) (a := 1)
      (by linarith) (by linarith)
    nlinarith
  · change (p 0 + -3 / 16) ^ 2 + (p 1 + 0) ^ 2 < 425 / 256
    have hx := square_lt_of_bounds (x := p 0 + -3 / 16) (a := 13 / 16)
      (by linarith) (by linarith)
    have hy := square_lt_of_bounds (x := p 1) (a := 1)
      (by linarith) (by linarith)
    nlinarith

theorem embedding_disjoint :
    Pairwise fun i j => Disjoint (embedding i '' UnitSquare) (embedding j '' UnitSquare) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, heq⟩
  rcases hp with ⟨hp0, hp1, hp2, hp3⟩
  rcases hq with ⟨hq0, hq1, hq2, hq3⟩
  have h0 := congrArg (fun z : Plane => z 0) heq
  have h1 := congrArg (fun z : Plane => z 1) heq
  simp only [embedding_apply] at h0 h1
  fin_cases i <;> fin_cases j <;>
    norm_num [offset, point] at h0 h1 hij <;> linarith

noncomputable def canonicalPacking : Packing 3 UnitSquare (Circle radius) where
  embeddings := embedding
  disjoint := embedding_disjoint
  inside := embedding_inside

/-- The known FC upper bound, with a kernel-checked proof. -/
theorem three_square_packing_in_circle_bound :
    Nonempty (Packing 3 UnitSquare (Circle ((5 * NNReal.sqrt 17) / 16))) :=
  ⟨canonicalPacking⟩

end ThreeSquares
