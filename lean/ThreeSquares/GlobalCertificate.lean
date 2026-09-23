import ThreeSquares.LocalConnection

/-! # Complete certificate trees and the global lower bound

For each of the 512 signed separation branches, a tree over the rotation
square `[0,1]²` ends only in leaves that exclude the branch: a first-order
interval certificate, a second-order certificate under a region hypothesis, or
a local certificate that moves the configuration into the neighborhood of the
T packing where `local_geometry_radius_lower_bound` applies.  A checked family
of such trees proves the unconditional lower bound.
-/

namespace ThreeSquares
namespace CenterElimination

open scoped NNReal
open SquarePacking

noncomputable section

inductive GTree where
  | reject (l : Fin 3 → Fin 4 → ℕ) (m : Fin 3 → ℕ)
  | qreject (l : Fin 3 → Fin 4 → ℕ) (m : Fin 3 → ℕ)
  | loc (D : LocalCert)
  | split (second : Bool) (left right : GTree)
  | diag (below above : GTree)
  | forget (T : GTree)
  | vacuous

namespace GTree

def check (code : ℕ) : GTree → TBox → ℤ → Bool
  | .reject l m, B, _ => (mkCert code l m).check (rotationBox B.a1 B.b1 B.a2 B.b2)
  | .qreject l m, B, region =>
      (mkCert code l m).qcheckFast (rotationBox B.a1 B.b1 B.a2 B.b2) region
  | .loc D, B, region => D.check code B region
  | .split second l r, B, region =>
      l.check code (B.left second) region && r.check code (B.right second) region
  | .diag l r, B, _ => l.check code B (-1) && r.check code B 1
  | .forget T, B, _ => T.check code B 0
  | .vacuous, B, region => decide ((region = 1 ∧ B.b1 < B.a2) ∨ (region = -1 ∧ B.b2 < B.a1))

def leafCount : GTree → ℕ
  | .reject _ _ | .qreject _ _ | .loc _ | .vacuous => 1
  | .split _ l r | .diag l r => l.leafCount + r.leafCount
  | .forget T => T.leafCount

theorem check_sound (T : GTree) (code : ℕ) (B : TBox) (region : ℤ) (hB : B.Inside)
    (hvr : QTree.ValidRegion region) (h : T.check code B region = true)
    {r : ℝ≥0} (P : RationalRotationPacking 3 r) (hr : r < radius) (h0 : P.t 0 = 0)
    (hreal : Realizes (P.toSubcritical hr) code) (ht : B.Contains (P.t 1) (P.t 2))
    (hreg : RegionHolds region (P.t 1) (P.t 2)) : False := by
  induction T generalizing B region with
  | reject l m =>
    obtain ⟨h1, h2, h3, h4⟩ := hB
    exact cert_excludes (mkCert code l m) h (P.toSubcritical hr) h0 hreal
      (by exact_mod_cast h1) ⟨ht.1, ht.2.1⟩ (by exact_mod_cast h2) (by exact_mod_cast h3)
      ⟨ht.2.2.1, ht.2.2.2⟩ (by exact_mod_cast h4)
  | qreject l m =>
    obtain ⟨h1, h2, h3, h4⟩ := hB
    simp only [check, qcheckFast_eq] at h
    exact qcert_excludes (mkCert code l m) region hvr h (P.toSubcritical hr) h0 hreal hreg
      (by exact_mod_cast h1) ⟨ht.1, ht.2.1⟩ (by exact_mod_cast h2) (by exact_mod_cast h3)
      ⟨ht.2.2.1, ht.2.2.2⟩ (by exact_mod_cast h4)
  | loc D => exact D.excludes code B region h P hr h0 hreal hB ht hvr hreg
  | split second l r hl hr' =>
    simp only [check, Bool.and_eq_true] at h
    rcases B.split_covers second ht with hc | hc
    · exact hl (B.left second) region (TBox.left_inside hB second hc) hvr h.1 hc hreg
    · exact hr' (B.right second) region (TBox.right_inside hB second hc) hvr h.2 hc hreg
  | diag l r hl hr' =>
    simp only [check, Bool.and_eq_true] at h
    rcases le_total (P.t 1) (P.t 2) with h12 | h21
    · exact hl B (-1) hB (Or.inl rfl) h.1 ht ⟨fun _ => h12, fun h => absurd h (by norm_num)⟩
    · exact hr' B 1 hB (Or.inr (Or.inr rfl)) h.2 ht ⟨fun h => absurd h (by norm_num), fun _ => h21⟩
  | forget T ih =>
    exact ih B 0 hB (Or.inr (Or.inl rfl)) h ht
      ⟨fun h => absurd h (lt_irrefl 0), fun h => absurd h (lt_irrefl 0)⟩
  | vacuous =>
    simp only [check, decide_eq_true_eq] at h
    obtain ⟨k1, k2, k3, k4⟩ := ht
    rcases h with ⟨rfl, hlt⟩ | ⟨rfl, hlt⟩
    · have h21 := hreg.2 (by norm_num)
      have : (B.b1 : ℝ) < B.a2 := by exact_mod_cast hlt
      linarith
    · have h12 := hreg.1 (by norm_num)
      have : (B.b2 : ℝ) < B.a1 := by exact_mod_cast hlt
      linarith

end GTree

structure CodedGTree where
  code : ℕ
  tree : GTree

/-- A checked family of complete trees for all 512 branches proves the
unconditional lower bound. -/
theorem global_lower_bound_of_trees (L : List CodedGTree)
    (hcodes : L.map CodedGTree.code = List.range 512)
    (hcheck : ∀ T ∈ L, T.tree.check T.code TBox.unit 0 = true) : GlobalLowerBound := by
  intro r hfeas
  by_contra hn
  have hr : r < radius := lt_of_not_ge hn
  obtain ⟨P, h0⟩ := (normalized_rational_rotation_packing_iff 3 r 0).mpr hfeas
  obtain ⟨code, hlt, hreal⟩ := exists_realized (P.toSubcritical hr) h0
  have hmem : code ∈ L.map CodedGTree.code := by rw [hcodes]; simpa using hlt
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hmem
  exact T.tree.check_sound T.code TBox.unit 0 (by simp [TBox.Inside, TBox.unit])
    (Or.inr (Or.inl rfl)) (hcheck T hT) P hr h0 hreal
    ⟨by simpa [TBox.unit] using P.t_nonneg 1, by simpa [TBox.unit] using P.t_le_one 1,
      by simpa [TBox.unit] using P.t_nonneg 2, by simpa [TBox.unit] using P.t_le_one 2⟩
    ⟨fun h => absurd h (lt_irrefl 0), fun h => absurd h (lt_irrefl 0)⟩

end

end CenterElimination
end ThreeSquares
