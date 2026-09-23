import ThreeSquares.IntervalCertificate
import Mathlib.Data.Fintype.Fin

/-! # Kernel-checked certificate examples and rejection controls

These small examples exercise retained leaves, complete exclusion, a split
boundary, empty input boxes, disjunction and invalid rejection. They are tests
of the checker, not a global certificate for the three-square problem.
-/

namespace ThreeSquares.CertificateExamples

def box : RationalBox 1 := fun _ => ⟨-2, 2⟩
def x : IntervalExpr 1 := .var 0
def unitConstraint : IntervalFormula 1 := .nonpos (.add (.square x) (.const (-1)))
def outsideConstraint : IntervalFormula 1 := .nonpos (.add (.const (3 / 2)) (.neg (.abs x)))
def impossible : IntervalFormula 1 := .conj unitConstraint outsideConstraint

def exclusion : IntervalCertificate 1 :=
  .split 0 (-5 / 4) .reject (.split 0 (5 / 4) .reject .reject)

theorem exclusion_accepted : exclusion.check impossible box = true := by decide +kernel
theorem exclusion_no_residuals : exclusion.residuals box = [] := by rfl

theorem example_infeasible : ¬ ∃ v : Fin 1 → ℝ, box.Contains v ∧ impossible.Holds v :=
  exclusion.exclude_sound impossible exclusion_accepted exclusion_no_residuals

def localization : IntervalCertificate 1 :=
  .split 0 (-5 / 4) .reject (.split 0 (5 / 4) .keep .reject)

theorem localization_accepted : localization.check unitConstraint box = true := by decide +kernel
theorem localization_has_one_residual : (localization.residuals box).length = 1 := by rfl

theorem invalid_rejection_refused :
    (IntervalCertificate.reject : IntervalCertificate 1).check unitConstraint box = false := by
  decide +kernel

def disjunction : IntervalFormula 1 :=
  .disj (.negative (.add (.const 3) x)) (.zero (.add (.const 3) (.neg x)))

theorem disjunction_refuted : disjunction.refute box = true := by decide +kernel

theorem empty_box_accepted :
    (IntervalCertificate.reject : IntervalCertificate 1).check
      (.nonpos (.const 0)) (fun _ => ⟨1, -1⟩) = true := by decide +kernel

theorem split_boundary_preserved :
    (box.splitLeft 0 0).Contains (fun _ => 0) ∧
      (box.splitRight 0 0).Contains (fun _ => 0) := by
  constructor <;> intro i <;> fin_cases i <;>
    norm_num [box, RationalBox.splitLeft, RationalBox.splitRight, RationalInterval.Contains]

theorem square_crossing_zero : (RationalInterval.square ⟨-2, 1⟩) = ⟨0, 4⟩ := by decide +kernel
theorem mixed_sign_product : RationalInterval.mul ⟨-2, 1⟩ ⟨-3, 4⟩ = ⟨-8, 6⟩ := by decide +kernel

theorem strict_boundary_refuted :
    (IntervalFormula.negative (.const 0) : IntervalFormula 1).refute box = true := by decide +kernel

theorem nonstrict_boundary_retained :
    (IntervalFormula.nonpos (.const 0) : IntervalFormula 1).refute box = false := by decide +kernel

end ThreeSquares.CertificateExamples
