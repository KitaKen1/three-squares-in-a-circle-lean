import ThreeSquares.ContractedPacking
import ThreeSquares.GeneratedCertificates.Focused6
import ThreeSquares.GeneratedCertificates.Focused8

/-! Concrete bounded searches on the contracted domain still leave boxes.
The localizations here cover all smaller-radius FC packings, including arbitrary
rotations and reflections; they do not assert that the residuals are empty. -/

open scoped NNReal
open SquarePacking

namespace ThreeSquares.PackingFormula

theorem focused6_box_eq : GeneratedCertificates.Focused6.box = contractedBox := by
  funext i
  fin_cases i <;> norm_num [GeneratedCertificates.Focused6.box, contractedBox]

theorem focused8_box_eq : GeneratedCertificates.Focused8.box = contractedBox := by
  funext i
  fin_cases i <;> norm_num [GeneratedCertificates.Focused8.box, contractedBox]

theorem focused6_localizes_smaller_fc_packing {r : ℝ≥0} (hr : r < radius)
    (h : Nonempty (Packing 3 UnitSquare (Circle r))) :
    ∃ x : Fin 15 → ℝ, ∃ C ∈ GeneratedCertificates.Focused6.certificate.residuals contractedBox,
      C.Contains x ∧ contractedFormula.Holds x := by
  apply contracted_certificate_localizes_smaller_fc_packing GeneratedCertificates.Focused6.certificate
    (by rw [← focused6_box_eq]; exact GeneratedCertificates.Focused6.accepted) hr h

theorem focused8_localizes_smaller_fc_packing {r : ℝ≥0} (hr : r < radius)
    (h : Nonempty (Packing 3 UnitSquare (Circle r))) :
    ∃ x : Fin 15 → ℝ, ∃ C ∈ GeneratedCertificates.Focused8.certificate.residuals contractedBox,
      C.Contains x ∧ contractedFormula.Holds x := by
  apply contracted_certificate_localizes_smaller_fc_packing GeneratedCertificates.Focused8.certificate
    (by rw [← focused8_box_eq]; exact GeneratedCertificates.Focused8.accepted) hr h

end ThreeSquares.PackingFormula
