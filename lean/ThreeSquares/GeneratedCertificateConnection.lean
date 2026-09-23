import ThreeSquares.PackingCertificate
import ThreeSquares.GeneratedCertificates.Initial6

/-! The bounded full-domain run applies to every smaller-radius FC packing.
Its 64 retained boxes still require further work; this is not a lower bound. -/

open scoped NNReal
open SquarePacking

namespace ThreeSquares.PackingFormula

theorem generated_initial_box_eq : GeneratedCertificates.Initial6.box = initialBox := by
  funext i
  fin_cases i <;> norm_num [GeneratedCertificates.Initial6.box, initialBox]

/-- All smaller-radius FC packings survive in one of the generated residual boxes. -/
theorem generated_initial_localizes_smaller_fc_packing {r : ℝ≥0} (hr : r < radius)
    (h : Nonempty (Packing 3 UnitSquare (Circle r))) :
    ∃ x : Fin 15 → ℝ, ∃ C ∈ GeneratedCertificates.Initial6.certificate.residuals initialBox,
      C.Contains x ∧ smallerFormula.Holds x := by
  apply certificate_localizes_smaller_fc_packing GeneratedCertificates.Initial6.certificate
    (by rw [← generated_initial_box_eq]; exact GeneratedCertificates.Initial6.accepted) hr h

end ThreeSquares.PackingFormula
