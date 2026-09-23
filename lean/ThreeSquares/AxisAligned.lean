import ThreeSquares.UpperBound

/-! # A lower bound for axis-aligned squares with T-shaped separation

This is a genuine lower-bound proof for a restricted class of configurations.
It does not establish that arbitrary rotated squares have this separation.
-/

noncomputable section

open scoped NNReal

namespace ThreeSquares

/-- Containment of all four vertices in the closed disk of radius `r`. -/
structure VertexBounds (r x y : ℝ) : Prop where
  leftDown : (x - 1 / 2) ^ 2 + (y - 1 / 2) ^ 2 ≤ r ^ 2
  leftUp : (x - 1 / 2) ^ 2 + (y + 1 / 2) ^ 2 ≤ r ^ 2
  rightDown : (x + 1 / 2) ^ 2 + (y - 1 / 2) ^ 2 ≤ r ^ 2
  rightUp : (x + 1 / 2) ^ 2 + (y + 1 / 2) ^ 2 ≤ r ^ 2

def positionalEnergy (a b c d e f : ℝ) : ℝ :=
  13 / 32 * ((a + 11 / 16) ^ 2 + b ^ 2) +
  19 / 64 * ((c - 5 / 16) ^ 2 + (d + 1 / 2) ^ 2 +
    (e - 5 / 16) ^ 2 + (f - 1 / 2) ^ 2)

theorem positionalEnergy_nonneg (a b c d e f : ℝ) :
    0 ≤ positionalEnergy a b c d e f := by
  unfold positionalEnergy
  positivity

theorem weighted_vertex_identity (a b c d e f : ℝ) :
    13 / 64 * ((a - 1 / 2) ^ 2 + (b - 1 / 2) ^ 2) +
    13 / 64 * ((a - 1 / 2) ^ 2 + (b + 1 / 2) ^ 2) +
    19 / 64 * ((c + 1 / 2) ^ 2 + (d - 1 / 2) ^ 2) +
    19 / 64 * ((e + 1 / 2) ^ 2 + (f + 1 / 2) ^ 2) =
      425 / 256 + positionalEnergy a b c d e f +
      247 / 512 * ((c - a - 1) + (e - a - 1)) + 19 / 32 * (f - d - 1) := by
  unfold positionalEnergy
  ring

/-- A quantitative lower bound whenever A is left of B,C and B is below C. -/
theorem axis_T_quantitative_bound {r a b c d e f : ℝ}
    (ha : VertexBounds r a b) (hb : VertexBounds r c d) (hc : VertexBounds r e f)
    (hab : 1 ≤ c - a) (hac : 1 ≤ e - a) (hbc : 1 ≤ f - d) :
    425 / 256 + positionalEnergy a b c d e f ≤ r ^ 2 := by
  have hi := weighted_vertex_identity a b c d e f
  nlinarith only [ha.leftDown, ha.leftUp, hb.rightDown, hc.rightUp, hi, hab, hac, hbc]

theorem axis_T_lower_bound {r : ℝ≥0} {a b c d e f : ℝ}
    (ha : VertexBounds r a b) (hb : VertexBounds r c d) (hc : VertexBounds r e f)
    (hab : 1 ≤ c - a) (hac : 1 ≤ e - a) (hbc : 1 ≤ f - d) :
    radius ≤ r := by
  have h := axis_T_quantitative_bound ha hb hc hab hac hbc
  have hQ := positionalEnergy_nonneg a b c d e f
  have hR := radius_sq_real
  have hn : (0 : ℝ) ≤ radius := radius.coe_nonneg
  have hr : (0 : ℝ) ≤ r := r.coe_nonneg
  change (radius : ℝ) ≤ r
  nlinarith

theorem axis_T_squared_lower_bound {r a b c d e f : ℝ}
    (ha : VertexBounds r a b) (hb : VertexBounds r c d) (hc : VertexBounds r e f)
    (hab : 1 ≤ c - a) (hac : 1 ≤ e - a) (hbc : 1 ≤ f - d) :
    425 / 256 ≤ r ^ 2 := by
  have h := axis_T_quantitative_bound ha hb hc hab hac hbc
  have hQ := positionalEnergy_nonneg a b c d e f
  linarith

theorem positionalEnergy_eq_zero_iff (a b c d e f : ℝ) :
    positionalEnergy a b c d e f = 0 ↔
      a = -11 / 16 ∧ b = 0 ∧ c = 5 / 16 ∧ d = -1 / 2 ∧ e = 5 / 16 ∧ f = 1 / 2 := by
  constructor
  · intro h
    unfold positionalEnergy at h
    have ha : (a + 11 / 16) ^ 2 = 0 := by
      nlinarith [sq_nonneg b, sq_nonneg (c - 5 / 16), sq_nonneg (d + 1 / 2),
        sq_nonneg (e - 5 / 16), sq_nonneg (f - 1 / 2)]
    have hb : b ^ 2 = 0 := by
      nlinarith [sq_nonneg (a + 11 / 16), sq_nonneg (c - 5 / 16), sq_nonneg (d + 1 / 2),
        sq_nonneg (e - 5 / 16), sq_nonneg (f - 1 / 2)]
    have hc : (c - 5 / 16) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a + 11 / 16), sq_nonneg b, sq_nonneg (d + 1 / 2),
        sq_nonneg (e - 5 / 16), sq_nonneg (f - 1 / 2)]
    have hd : (d + 1 / 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a + 11 / 16), sq_nonneg b, sq_nonneg (c - 5 / 16),
        sq_nonneg (e - 5 / 16), sq_nonneg (f - 1 / 2)]
    have he : (e - 5 / 16) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a + 11 / 16), sq_nonneg b, sq_nonneg (c - 5 / 16),
        sq_nonneg (d + 1 / 2), sq_nonneg (f - 1 / 2)]
    have hf : (f - 1 / 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a + 11 / 16), sq_nonneg b, sq_nonneg (c - 5 / 16),
        sq_nonneg (d + 1 / 2), sq_nonneg (e - 5 / 16)]
    have ha' := (sq_eq_zero_iff.mp ha)
    have hb' := (sq_eq_zero_iff.mp hb)
    have hc' := (sq_eq_zero_iff.mp hc)
    have hd' := (sq_eq_zero_iff.mp hd)
    have he' := (sq_eq_zero_iff.mp he)
    have hf' := (sq_eq_zero_iff.mp hf)
    exact ⟨by linarith, hb', by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    norm_num [positionalEnergy]

theorem axis_T_rigidity {a b c d e f : ℝ}
    (ha : VertexBounds radius a b) (hb : VertexBounds radius c d)
    (hc : VertexBounds radius e f)
    (hab : 1 ≤ c - a) (hac : 1 ≤ e - a) (hbc : 1 ≤ f - d) :
    a = -11 / 16 ∧ b = 0 ∧ c = 5 / 16 ∧ d = -1 / 2 ∧ e = 5 / 16 ∧ f = 1 / 2 := by
  apply (positionalEnergy_eq_zero_iff a b c d e f).mp
  have h := axis_T_quantitative_bound ha hb hc hab hac hbc
  have hQ := positionalEnergy_nonneg a b c d e f
  rw [radius_sq_real] at h
  linarith

end ThreeSquares
