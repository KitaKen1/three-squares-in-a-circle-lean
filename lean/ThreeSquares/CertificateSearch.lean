import ThreeSquares.IntervalCertificate

/-! A bounded, deterministic certificate generator. Exhausted searches retain
their boxes. The generated tree is also exported and independently checked. -/

namespace ThreeSquares
namespace RationalBox

/-- Choose the first widest positive-width coordinate; ties are deterministic. -/
def bisect {n : ℕ} (B : RationalBox n) : Option (Fin n × ℚ) := Id.run do
  let mut best : Option (Fin n) := none
  for i in List.finRange n do
    if (B i).lo < (B i).hi then
      match best with
      | none => best := some i
      | some j =>
        if (B j).hi - (B j).lo < (B i).hi - (B i).lo then best := some i
  return best.map fun i => (i, ((B i).lo + (B i).hi) / 2)

end RationalBox
namespace IntervalCertificate

def search {n : ℕ} (p : IntervalFormula n) (B : RationalBox n) : ℕ → IntervalCertificate n
  | 0 => if B.isEmpty || p.refute B then .reject else .keep
  | d + 1 =>
    if B.isEmpty || p.refute B then .reject
    else match B.bisect with
      | none => .keep
      | some (i, q) => .split i q
          (search p (B.splitLeft i q) d) (search p (B.splitRight i q) d)

def nodeCount {n : ℕ} : IntervalCertificate n → ℕ
  | .reject | .keep => 1
  | .split _ _ l r => 1 + l.nodeCount + r.nodeCount

def keptCount {n : ℕ} : IntervalCertificate n → ℕ
  | .reject => 0
  | .keep => 1
  | .split _ _ l r => l.keptCount + r.keptCount

def rejectedCount {n : ℕ} : IntervalCertificate n → ℕ
  | .reject => 1
  | .keep => 0
  | .split _ _ l r => l.rejectedCount + r.rejectedCount

def depth {n : ℕ} : IntervalCertificate n → ℕ
  | .reject | .keep => 0
  | .split _ _ l r => 1 + max l.depth r.depth

theorem search_accepted {n : ℕ} (p : IntervalFormula n) (B : RationalBox n) (d : ℕ) :
    (search p B d).check p B = true := by
  induction d generalizing B with
  | zero =>
    simp only [search]
    split <;> simp_all [check]
  | succ d ih =>
    simp only [search]
    split
    · simp_all [check]
    · split
      · rfl
      · simp only [check, ih, Bool.and_self]

theorem residuals_length {n : ℕ} (t : IntervalCertificate n) (B : RationalBox n) :
    (t.residuals B).length = t.keptCount := by
  induction t generalizing B with
  | reject => rfl
  | keep => rfl
  | split i q l r hl hr => simp only [residuals, List.length_append, keptCount, hl, hr]

theorem search_depth_le {n : ℕ} (p : IntervalFormula n) (B : RationalBox n) (d : ℕ) :
    (search p B d).depth ≤ d := by
  induction d generalizing B with
  | zero => simp only [search]; split <;> simp [depth]
  | succ d ih =>
    simp only [search]
    split
    · simp [depth]
    · split
      · simp [depth]
      · simpa only [depth, Nat.add_comm 1] using
          Nat.succ_le_succ (max_le (ih _) (ih _))

theorem nodeCount_le {n : ℕ} (t : IntervalCertificate n) :
    t.nodeCount + 1 ≤ 2 ^ (t.depth + 1) := by
  induction t with
  | reject => simp [nodeCount, depth]
  | keep => simp [nodeCount, depth]
  | split i q l r hl hr =>
    have hl' : 2 ^ (l.depth + 1) ≤ 2 ^ (max l.depth r.depth + 1) :=
      Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right (le_max_left _ _) 1)
    have hr' : 2 ^ (r.depth + 1) ≤ 2 ^ (max l.depth r.depth + 1) :=
      Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right (le_max_right _ _) 1)
    calc
      (split i q l r).nodeCount + 1 = (l.nodeCount + 1) + (r.nodeCount + 1) := by
        simp only [nodeCount]; omega
      _ ≤ 2 ^ (max l.depth r.depth + 1) + 2 ^ (max l.depth r.depth + 1) :=
        Nat.add_le_add (hl.trans hl') (hr.trans hr')
      _ = 2 ^ ((split i q l r).depth + 1) := by
        simp only [depth]
        rw [Nat.add_comm 1 (max l.depth r.depth), pow_succ]
        omega

theorem search_localizes {n : ℕ} (p : IntervalFormula n) (B : RationalBox n) (d : ℕ)
    {x : Fin n → ℝ} (hx : B.Contains x) (hp : p.Holds x) :
    ∃ C ∈ (search p B d).residuals B, C.Contains x :=
  (search p B d).check_sound p (search_accepted p B d) hx hp

theorem search_excludes_of_no_kept {n : ℕ} (p : IntervalFormula n)
    (B : RationalBox n) (d : ℕ) (h : (search p B d).keptCount = 0) :
    ¬ ∃ x : Fin n → ℝ, B.Contains x ∧ p.Holds x := by
  apply (search p B d).exclude_sound p (search_accepted p B d)
  exact List.length_eq_zero_iff.mp ((residuals_length _ _).trans h)

end IntervalCertificate
end ThreeSquares
