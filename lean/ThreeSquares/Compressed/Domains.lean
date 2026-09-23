import ThreeSquares.Compressed.EditorInfo
import ThreeSquares.Compressed.Bernstein
import ThreeSquares.BranchSymmetry

namespace ThreeSquares.CenterElimination.Compressed
open scoped NNReal
open SquarePacking

/-- A local branch exclusion, with no computational tree stored in the term. -/
def Excludes (code : ℕ) (B : TBox) (region : ℤ) : Prop :=
  ∀ P : SubcriticalRationalRotationPacking 3, P.t 0 = 0 → Realizes P code →
    B.Contains (P.t 1) (P.t 2) → RegionHolds region (P.t 1) (P.t 2) → False

theorem excludes_split (code : ℕ) (B : TBox) (region : ℤ) (second : Bool)
    (hl : Excludes code (B.left second) region)
    (hr : Excludes code (B.right second) region) : Excludes code B region := by
  intro P h0 hreal ht hreg
  rcases B.split_covers second ht with h | h
  · exact hl P h0 hreal h hreg
  · exact hr P h0 hreal h hreg

theorem excludes_diag (code : ℕ) (B : TBox) (region : ℤ)
    (hl : Excludes code B (-1)) (hr : Excludes code B 1) : Excludes code B region := by
  intro P h0 hreal ht _
  rcases le_total (P.t 1) (P.t 2) with h | h
  · exact hl P h0 hreal ht ⟨fun _ => h, fun h => absurd h (by norm_num)⟩
  · exact hr P h0 hreal ht ⟨fun h => absurd h (by norm_num), fun _ => h⟩

theorem excludes_forget (code : ℕ) (B : TBox) (region : ℤ)
    (h : Excludes code B 0) : Excludes code B region := by
  intro P h0 hreal ht _
  exact h P h0 hreal ht
    ⟨fun h => absurd h (lt_irrefl 0), fun h => absurd h (lt_irrefl 0)⟩

theorem excludes_of_numerator (code : ℕ) (B : TBox) (region : ℤ)
    (C : Certificate) (hc : C.code = code) (a : Seven) (n : Numerator) (σ : Fin 3 → ℚ)
    (hw : C.wellFormed = true)
    (hσ : ∀ e, σ e = 1 ∨ σ e = -1 ∨ σ e = 0)
    (hmatch : quadMatches (C.lowerQuad σ) a = true)
    (hn : n = numerator a)
    (hpos : ∀ x y : ℝ, B.Contains x y → RegionHolds region x y → 0 ≤ numEval n x y) :
    Excludes code B region := by
  intro P h0 hreal ht hreg
  apply certificate_excludes C a σ hw hσ hmatch P h0
  · simpa only [hc] using hreal
  · rw [← hn]
    exact hpos _ _ ht hreg

theorem global_lower_bound_of_excludes (codes : List ℕ) (word : ℕ → ℕ × Bool)
    (hword : ∀ c, c < 512 → applyCode (word c).1 (word c).2 c ∈ codes)
    (hex : ∀ c ∈ codes, Excludes c TBox.unit 0) : GlobalLowerBound := by
  intro r hfeas
  by_contra hn
  have hr : r < radius := lt_of_not_ge hn
  obtain ⟨P, h0⟩ := (normalized_rational_rotation_packing_iff 3 r 0).mpr hfeas
  obtain ⟨c, hlt, hreal⟩ := exists_realized (P.toSubcritical hr) h0
  let P' := applyPacking (word c).1 (word c).2 P
  have h0' : P'.t 0 = 0 := by rw [applyPacking_t0]; exact h0
  have hreal' := realizes_apply P hr (word c).1 (word c).2 c hreal
  exact hex _ (hword c hlt) (P'.toSubcritical hr) h0' hreal'
    ⟨by simpa [TBox.unit] using (P'.toSubcritical hr).t_nonneg 1, by simpa [TBox.unit] using (P'.toSubcritical hr).t_le_one 1,
      by simpa [TBox.unit] using (P'.toSubcritical hr).t_nonneg 2, by simpa [TBox.unit] using (P'.toSubcritical hr).t_le_one 2⟩
    ⟨fun h => absurd h (lt_irrefl 0), fun h => absurd h (lt_irrefl 0)⟩

theorem excludes_of_scaled_numerator (code : ℕ) (B : TBox) (region : ℤ)
    (C : Certificate) (hc : C.code = code) (a : Seven) (n : Numerator) (σ : Fin 3 → ℚ)
    (hw : C.wellFormed = true)
    (hσ : ∀ e, σ e = 1 ∨ σ e = -1 ∨ σ e = 0)
    (hmatch : quadMatches (C.lowerQuad σ) a = true)
    (d : ℚ) (hd : 0 < d) (hn : n = fun i j => d * numerator a i j)
    (hpos : ∀ x y : ℝ, B.Contains x y → RegionHolds region x y → 0 ≤ numEval n x y) :
    Excludes code B region := by
  apply excludes_of_numerator code B region C hc a (numerator a) σ hw hσ hmatch rfl
  intro x y hb hr
  have h := hpos x y hb hr
  rw [hn, numEval_scale] at h
  exact (mul_nonneg_iff_of_pos_left (show (0 : ℝ) < d by exact_mod_cast hd)).mp h

#print axioms global_lower_bound_of_excludes
end ThreeSquares.CenterElimination.Compressed
