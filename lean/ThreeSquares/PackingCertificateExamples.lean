import ThreeSquares.PackingFormula

/-! # Small certificates using the actual packing formula

An entire box of overlapping squares is excluded. The known optimal-radius
construction is retained, including exact boundary contacts. These checks
are reduced by Lean's kernel, not by a native-code decision oracle.
-/

namespace ThreeSquares.PackingCertificateExamples

def overlapBox : RationalBox 15 :=
  ![⟨-1 / 8, 1 / 8⟩, ⟨-1 / 8, 1 / 8⟩,
    ⟨-1 / 8, 1 / 8⟩, ⟨-1 / 8, 1 / 8⟩,
    ⟨-1 / 8, 1 / 8⟩, ⟨-1 / 8, 1 / 8⟩,
    .singleton 1, .singleton 0, .singleton 0, .singleton 1,
    .singleton 1, .singleton 0, .singleton 0, .singleton 1, .singleton 2]

theorem overlapping_pair_refuted : (PackingFormula.pair 0 1).refute overlapBox = true := by
  decide +kernel

theorem overlap_certificate_accepted :
    (IntervalCertificate.reject : IntervalCertificate 15).check PackingFormula.formula overlapBox = true := by
  decide +kernel

theorem overlap_box_infeasible :
    ¬ ∃ x : Fin 15 → ℝ, overlapBox.Contains x ∧ PackingFormula.formula.Holds x :=
  IntervalCertificate.exclude_sound .reject PackingFormula.formula overlap_certificate_accepted rfl

def canonicalBox : RationalBox 15 :=
  ![.singleton (-11 / 16), .singleton 0, .singleton (5 / 16), .singleton (-1 / 2),
    .singleton (5 / 16), .singleton (1 / 2),
    .singleton 1, .singleton 0, .singleton 0, .singleton 1,
    .singleton 1, .singleton 0, .singleton 0, .singleton 1, .singleton (425 / 256)]

theorem canonical_contact_not_refuted : PackingFormula.formula.refute canonicalBox = false := by
  decide +kernel

theorem invalid_canonical_rejection_refused :
    (IntervalCertificate.reject : IntervalCertificate 15).check PackingFormula.formula canonicalBox = false := by
  decide +kernel

end ThreeSquares.PackingCertificateExamples
