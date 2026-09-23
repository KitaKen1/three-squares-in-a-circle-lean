import ThreeSquares.CertificateSearch

/-! Search heuristics may change freely: all selected splits preserve coverage.
The emitted tree is checked independently of the heuristic that produced it. -/

namespace ThreeSquares
namespace RationalBox

def bisectWeighted {n : ℕ} (weights : Fin n → ℚ) (B : RationalBox n) :
    Option (Fin n × ℚ) := Id.run do
  let mut best : Option (Fin n) := none
  for i in List.finRange n do
    if (B i).lo < (B i).hi then
      match best with
      | none => best := some i
      | some j =>
        if weights j * ((B j).hi - (B j).lo) < weights i * ((B i).hi - (B i).lo) then
          best := some i
  return best.map fun i => (i, ((B i).lo + (B i).hi) / 2)

end RationalBox
namespace IntervalCertificate

def searchWith {n : ℕ} (choose : RationalBox n → Option (Fin n × ℚ))
    (p : IntervalFormula n) (B : RationalBox n) : ℕ → IntervalCertificate n
  | 0 => if B.isEmpty || p.refute B then .reject else .keep
  | d + 1 => if B.isEmpty || p.refute B then .reject
    else match choose B with
      | none => .keep
      | some (i, q) => .split i q
          (searchWith choose p (B.splitLeft i q) d)
          (searchWith choose p (B.splitRight i q) d)

def searchWeighted {n : ℕ} (weights : Fin n → ℚ) :=
  @searchWith n (RationalBox.bisectWeighted weights)

theorem searchWith_accepted {n : ℕ} (choose : RationalBox n → Option (Fin n × ℚ))
    (p : IntervalFormula n) (B : RationalBox n) (d : ℕ) :
    (searchWith choose p B d).check p B = true := by
  induction d generalizing B with
  | zero => simp only [searchWith]; split <;> simp_all [check]
  | succ d ih =>
    simp only [searchWith]
    split
    · simp_all [check]
    · split
      · rfl
      · simp only [check, ih, Bool.and_self]

theorem searchWith_depth_le {n : ℕ} (choose : RationalBox n → Option (Fin n × ℚ))
    (p : IntervalFormula n) (B : RationalBox n) (d : ℕ) :
    (searchWith choose p B d).depth ≤ d := by
  induction d generalizing B with
  | zero => simp only [searchWith]; split <;> simp [depth]
  | succ d ih =>
    simp only [searchWith]
    split
    · simp [depth]
    · split
      · simp [depth]
      · simpa only [depth, Nat.add_comm 1] using
          Nat.succ_le_succ (max_le (ih _) (ih _))

theorem searchWith_localizes {n : ℕ} (choose : RationalBox n → Option (Fin n × ℚ))
    (p : IntervalFormula n) (B : RationalBox n) (d : ℕ)
    {x : Fin n → ℝ} (hx : B.Contains x) (hp : p.Holds x) :
    ∃ C ∈ (searchWith choose p B d).residuals B, C.Contains x :=
  (searchWith choose p B d).check_sound p (searchWith_accepted choose p B d) hx hp

theorem searchWith_excludes_of_no_kept {n : ℕ}
    (choose : RationalBox n → Option (Fin n × ℚ)) (p : IntervalFormula n)
    (B : RationalBox n) (d : ℕ) (h : (searchWith choose p B d).keptCount = 0) :
    ¬ ∃ x : Fin n → ℝ, B.Contains x ∧ p.Holds x := by
  apply (searchWith choose p B d).exclude_sound p (searchWith_accepted choose p B d)
  exact List.length_eq_zero_iff.mp ((residuals_length _ _).trans h)

end IntervalCertificate
end ThreeSquares
