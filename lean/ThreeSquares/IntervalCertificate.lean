import ThreeSquares.IntervalExpression

/-! # A sound certificate checker for splitting, exclusion and residual boxes

The certificate supplies splitting coordinates and rational cut points only.
Child boxes are computed by the checker and include the shared boundary.
Rejected leaves require a verified interval contradiction; retained leaves
are returned explicitly. Accepting a tree does not mean that its residual
boxes are empty, or that the square-packing lower bound has been proved.
-/

namespace ThreeSquares

namespace RationalBox

def splitLeft {n : ℕ} (B : RationalBox n) (i : Fin n) (q : ℚ) : RationalBox n :=
  Function.update B i ⟨(B i).lo, min (B i).hi q⟩

def splitRight {n : ℕ} (B : RationalBox n) (i : Fin n) (q : ℚ) : RationalBox n :=
  Function.update B i ⟨max (B i).lo q, (B i).hi⟩

theorem split_covers {n : ℕ} {B : RationalBox n} {x : Fin n → ℝ}
    (hx : B.Contains x) (i : Fin n) (q : ℚ) :
    (B.splitLeft i q).Contains x ∨ (B.splitRight i q).Contains x := by
  by_cases hq : x i ≤ (q : ℝ)
  · left
    intro j
    by_cases hj : j = i
    · subst j
      simp only [splitLeft, Function.update_self, RationalInterval.Contains, Rat.cast_min]
      exact ⟨(hx i).1, le_min (hx i).2 hq⟩
    · simpa only [splitLeft, Function.update_of_ne hj] using hx j
  · right
    intro j
    by_cases hj : j = i
    · subst j
      simp only [splitRight, Function.update_self, RationalInterval.Contains, Rat.cast_max]
      exact ⟨max_le (hx i).1 (le_of_lt (lt_of_not_ge hq)), (hx i).2⟩
    · simpa only [splitRight, Function.update_of_ne hj] using hx j

theorem splitLeft_subset {n : ℕ} {B : RationalBox n} {x : Fin n → ℝ}
    {i : Fin n} {q : ℚ} (hx : (B.splitLeft i q).Contains x) : B.Contains x := by
  intro j
  by_cases hj : j = i
  · subst j
    have h := hx i
    simp only [splitLeft, Function.update_self, RationalInterval.Contains, Rat.cast_min] at h
    exact ⟨h.1, h.2.trans (min_le_left _ _)⟩
  · simpa only [splitLeft, Function.update_of_ne hj] using hx j

theorem splitRight_subset {n : ℕ} {B : RationalBox n} {x : Fin n → ℝ}
    {i : Fin n} {q : ℚ} (hx : (B.splitRight i q).Contains x) : B.Contains x := by
  intro j
  by_cases hj : j = i
  · subst j
    have h := hx i
    simp only [splitRight, Function.update_self, RationalInterval.Contains, Rat.cast_max] at h
    exact ⟨(le_max_left _ _).trans h.1, h.2⟩
  · simpa only [splitRight, Function.update_of_ne hj] using hx j

def isEmpty {n : ℕ} (B : RationalBox n) : Bool :=
  (List.finRange n).any (fun i => decide ((B i).hi < (B i).lo))

theorem isEmpty_sound {n : ℕ} {B : RationalBox n} (h : B.isEmpty = true)
    (x : Fin n → ℝ) : ¬ B.Contains x := by
  have he : ∃ i : Fin n, (B i).hi < (B i).lo := by simpa [isEmpty] using h
  obtain ⟨i, hi⟩ := he
  intro hx
  exact RationalInterval.not_contains_of_empty hi (x i) (hx i)

end RationalBox

inductive IntervalCertificate (n : ℕ) where
  | reject
  | keep
  | split (i : Fin n) (q : ℚ) (left right : IntervalCertificate n)
  deriving Repr, DecidableEq

namespace IntervalCertificate

def check {n : ℕ} (p : IntervalFormula n) (B : RationalBox n) : IntervalCertificate n → Bool
  | .reject => B.isEmpty || p.refute B
  | .keep => true
  | .split i q l r => l.check p (B.splitLeft i q) && r.check p (B.splitRight i q)

def residuals {n : ℕ} (B : RationalBox n) : IntervalCertificate n → List (RationalBox n)
  | .reject => []
  | .keep => [B]
  | .split i q l r => l.residuals (B.splitLeft i q) ++ r.residuals (B.splitRight i q)

/-- Every feasible point of the input box survives in an explicit retained leaf. -/
theorem check_sound {n : ℕ} (t : IntervalCertificate n) (p : IntervalFormula n)
    {B : RationalBox n} (hcheck : t.check p B = true) {x : Fin n → ℝ}
    (hx : B.Contains x) (hp : p.Holds x) :
    ∃ C ∈ t.residuals B, C.Contains x := by
  induction t generalizing B with
  | reject =>
    have hr : B.isEmpty = true ∨ p.refute B = true := by simpa [check] using hcheck
    rcases hr with h | h
    · exact False.elim (RationalBox.isEmpty_sound h x hx)
    · exact False.elim (p.refute_sound hx h hp)
  | keep => exact ⟨B, by simp [residuals], hx⟩
  | split i q l r hl hr =>
    have hc : l.check p (B.splitLeft i q) = true ∧
        r.check p (B.splitRight i q) = true := by simpa [check] using hcheck
    rcases RationalBox.split_covers hx i q with h | h
    · obtain ⟨C, hC, hxC⟩ := hl hc.1 h
      exact ⟨C, by simp only [residuals, List.mem_append]; exact Or.inl hC, hxC⟩
    · obtain ⟨C, hC, hxC⟩ := hr hc.2 h
      exact ⟨C, by simp only [residuals, List.mem_append]; exact Or.inr hC, hxC⟩

/-- An accepted certificate proves infeasibility only when no leaves remain. -/
theorem exclude_sound {n : ℕ} (t : IntervalCertificate n) (p : IntervalFormula n)
    {B : RationalBox n} (hcheck : t.check p B = true) (hempty : t.residuals B = []) :
    ¬ ∃ x : Fin n → ℝ, B.Contains x ∧ p.Holds x := by
  rintro ⟨x, hx, hp⟩
  obtain ⟨C, hC, _⟩ := t.check_sound p hcheck hx hp
  simp [hempty] at hC

theorem residual_subset {n : ℕ} (t : IntervalCertificate n) {B C : RationalBox n}
    (hC : C ∈ t.residuals B) {x : Fin n → ℝ} (hx : C.Contains x) : B.Contains x := by
  induction t generalizing B with
  | reject => simp [residuals] at hC
  | keep =>
    have h : C = B := by simpa [residuals] using hC
    simpa only [h] using hx
  | split i q l r hl hr =>
    have h : C ∈ l.residuals (B.splitLeft i q) ∨ C ∈ r.residuals (B.splitRight i q) := by
      simpa only [residuals, List.mem_append] using hC
    rcases h with h | h
    · exact RationalBox.splitLeft_subset (hl h)
    · exact RationalBox.splitRight_subset (hr h)

end IntervalCertificate
end ThreeSquares
