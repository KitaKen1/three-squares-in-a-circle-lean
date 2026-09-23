import ThreeSquares.StrictBound
import Mathlib.Tactic.LinearCombination

/-! # Seven-coefficient representation for sums of three rotated vectors

This is the production-library version of the algebraic identity in
`research/SevenCoefficientIdentity.lean`. It packages the constant, the two
single-angle pairs, and the two relative-angle coefficients. The remaining
工程2 obligation is to construct these vectors and the piecewise width terms
from an actual `Certificate`.
-/

namespace ThreeSquares
namespace CenterElimination

structure SevenCoefficients where
  constant : ℝ
  cosOne : ℝ
  sinOne : ℝ
  cosTwo : ℝ
  sinTwo : ℝ
  cosDifference : ℝ
  sinDifference : ℝ

def SevenCoefficients.eval (a : SevenCoefficients)
    (c₁ s₁ c₂ s₂ : ℝ) : ℝ :=
  a.constant + a.cosOne * c₁ + a.sinOne * s₁ +
    a.cosTwo * c₂ + a.sinTwo * s₂ +
    a.cosDifference * (c₁ * c₂ + s₁ * s₂) +
    a.sinDifference * (c₁ * s₂ - s₁ * c₂)

def rotatedResidualCoefficients
    (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) : SevenCoefficients where
  constant := x₀ ^ 2 + y₀ ^ 2 + x₁ ^ 2 + y₁ ^ 2 + x₂ ^ 2 + y₂ ^ 2
  cosOne := 2 * (x₀ * x₁ + y₀ * y₁)
  sinOne := 2 * (y₀ * x₁ - x₀ * y₁)
  cosTwo := 2 * (x₀ * x₂ + y₀ * y₂)
  sinTwo := 2 * (y₀ * x₂ - x₀ * y₂)
  cosDifference := 2 * (x₁ * x₂ + y₁ * y₂)
  sinDifference := 2 * (y₁ * x₂ - x₁ * y₂)

/-- The squared norm of three rotated planar vectors has exactly the seven
constant/single-angle/relative-angle coefficients above. -/
theorem rotatedResidual_seven_coefficients
    (x₀ y₀ x₁ y₁ x₂ y₂ c₁ s₁ c₂ s₂ : ℝ)
    (h₁ : c₁ ^ 2 + s₁ ^ 2 = 1) (h₂ : c₂ ^ 2 + s₂ ^ 2 = 1) :
    (x₀ + c₁ * x₁ - s₁ * y₁ + c₂ * x₂ - s₂ * y₂) ^ 2 +
        (y₀ + s₁ * x₁ + c₁ * y₁ + s₂ * x₂ + c₂ * y₂) ^ 2 =
      (rotatedResidualCoefficients x₀ y₀ x₁ y₁ x₂ y₂).eval c₁ s₁ c₂ s₂ := by
  unfold SevenCoefficients.eval rotatedResidualCoefficients
  linear_combination (x₁ ^ 2 + y₁ ^ 2) * h₁ + (x₂ ^ 2 + y₂ ^ 2) * h₂

#print axioms rotatedResidual_seven_coefficients

end CenterElimination
end ThreeSquares
