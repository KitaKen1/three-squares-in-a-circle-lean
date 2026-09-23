import ThreeSquares.QuadFast

/-! # Connecting residual rotation boxes to the local lower bound

A residual box of the center-eliminating certificates lies next to an
axis-parallel orientation.  There the completed squares bound the distance of
every center from an explicit rational enclosure.  A global rotation that makes
the top square axis-parallel, one of the eight square symmetries and internal
quarter turns then present the three squares exactly in the coordinates of
`local_geometry_radius_lower_bound`, whose perturbation bound is checked by
interval arithmetic.
-/

namespace ThreeSquares

open scoped NNReal
open SquarePacking Set

noncomputable section

/- ## Global rotations -/

/-- Inverse of the rotation with cosine `u` and sine `v`. -/
def rotInv (u v : ℝ) (z : Plane) : Plane := point (u * z 0 + v * z 1) (-v * z 0 + u * z 1)

theorem rotInv_add (u v : ℝ) (z w : Plane) :
    rotInv u v (z + w) = rotInv u v z + rotInv u v w := by
  ext k; fin_cases k <;> simp [rotInv, point] <;> ring

theorem rotInv_norm_sq {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1) (z : Plane) :
    rotInv u v z 0 ^ 2 + rotInv u v z 1 ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
  simp only [rotInv, point_zero, point_one]
  linear_combination (z 0 ^ 2 + z 1 ^ 2) * huv

theorem rotInv_injective {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1) :
    Function.Injective (rotInv u v) := by
  intro z w h
  have h0 := congrArg (fun p : Plane => p 0) h
  have h1 := congrArg (fun p : Plane => p 1) h
  simp only [rotInv, point_zero, point_one] at h0 h1
  ext k
  fin_cases k
  · show z 0 = w 0
    linear_combination u * h0 - v * h1 - (z 0 - w 0) * huv
  · show z 1 = w 1
    linear_combination v * h0 + u * h1 - (z 1 - w 1) * huv

theorem rotInv_mem_circle_iff {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1) (r : ℝ≥0) (z : Plane) :
    rotInv u v z ∈ Circle r ↔ z ∈ Circle r := by
  change rotInv u v z 0 ^ 2 + rotInv u v z 1 ^ 2 < (r : ℝ) ^ 2 ↔ z 0 ^ 2 + z 1 ^ 2 < (r : ℝ) ^ 2
  rw [rotInv_norm_sq huv]

theorem rotInv_rotation {u v a p : ℝ} (_huv : u ^ 2 + v ^ 2 = 1) (hap : a ^ 2 + p ^ 2 = 1)
    (h' : (u * a + v * p) ^ 2 + (u * p - v * a) ^ 2 = 1) (w : Plane) :
    rotInv u v ((rotationCoefficients a p hap).toFrame w) =
      (rotationCoefficients (u * a + v * p) (u * p - v * a) h').toFrame w := by
  ext k; fin_cases k <;> simp [rotInv, rotationCoefficients, point] <;> ring

theorem rotation_difference_unit {u v a p : ℝ} (huv : u ^ 2 + v ^ 2 = 1)
    (hap : a ^ 2 + p ^ 2 = 1) : (u * a + v * p) ^ 2 + (u * p - v * a) ^ 2 = 1 := by
  linear_combination (a ^ 2 + p ^ 2) * huv + hap

theorem placedSquare_rotInv {u v a p : ℝ} (huv : u ^ 2 + v ^ 2 = 1)
    (hap : a ^ 2 + p ^ 2 = 1) (c : Plane) :
    placedSquare (rotInv u v c)
        (rotationCoefficients (u * a + v * p) (u * p - v * a)
          (rotation_difference_unit huv hap)).toFrame =
      rotInv u v '' placedSquare c (rotationCoefficients a p hap).toFrame := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨c + (rotationCoefficients a p hap).toFrame w, ⟨w, hw, rfl⟩,
      by rw [rotInv_add, rotInv_rotation huv hap]⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, by rw [rotInv_add, rotInv_rotation huv hap]⟩

/- ## Quarter turns -/

/-- Cosine and sine after `k` internal quarter turns. -/
def turnA : Fin 4 → ℝ → ℝ → ℝ := ![fun a _ => a, fun _ p => -p, fun a _ => -a, fun _ p => p]
def turnP : Fin 4 → ℝ → ℝ → ℝ := ![fun _ p => p, fun a _ => a, fun _ p => -p, fun a _ => -a]

theorem turn_unit (k : Fin 4) {a p : ℝ} (h : a ^ 2 + p ^ 2 = 1) :
    turnA k a p ^ 2 + turnP k a p ^ 2 = 1 := by
  fin_cases k <;> simp [turnA, turnP] <;> nlinarith [h]

theorem placedSquare_turn (k : Fin 4) (c : Plane) {a p : ℝ} (h : a ^ 2 + p ^ 2 = 1) :
    placedSquare c (rotationCoefficients a p h).toFrame =
      placedSquare c (rotationCoefficients (turnA k a p) (turnP k a p) (turn_unit k h)).toFrame := by
  have h1 : (-p) ^ 2 + a ^ 2 = 1 := by nlinarith [h]
  have h2 : (-a) ^ 2 + (-p) ^ 2 = 1 := by nlinarith [h]
  have h3 : p ^ 2 + (-a) ^ 2 = 1 := by nlinarith [h]
  have q1 : placedSquare c (rotationCoefficients a p h).toFrame =
      placedSquare c (rotationCoefficients (-p) a h1).toFrame :=
    placedSquare_rotation_quarter c h
  have q2 : placedSquare c (rotationCoefficients (-p) a h1).toFrame =
      placedSquare c (rotationCoefficients (-a) (-p) h2).toFrame := by
    simpa using placedSquare_rotation_quarter c h1
  have q3 : placedSquare c (rotationCoefficients (-a) (-p) h2).toFrame =
      placedSquare c (rotationCoefficients p (-a) h3).toFrame := by
    simpa using placedSquare_rotation_quarter c h2
  fin_cases k
  · rfl
  · exact q1
  · exact q1.trans q2
  · exact q1.trans (q2.trans q3)

/- ## The local lower bound for placed squares -/

theorem rotationCoefficients_one_zero :
    rotationCoefficients 1 0 (by norm_num) = identityCoefficients := by
  ext <;> simp [rotationCoefficients, identityCoefficients]

/-- The local lower bound in terms of placed sets. -/
theorem local_sets_lower_bound {r : ℝ≥0} (hr : r < radius)
    {x₁ y₁ x₂ y₂ x₃ y₃ a p b q : ℝ}
    (haunit : a ^ 2 + p ^ 2 = 1) (hbunit : b ^ 2 + q ^ 2 = 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsmall : perturbation x₁ y₁ x₂ y₂ x₃ y₃ p q ≤ 1 / 64)
    (L R T : Set Plane)
    (hL : L = placedSquare (point (-1 / 2 + x₁) (-5 / 16 + y₁))
      (rotationCoefficients a p haunit).toFrame)
    (hR : R = placedSquare (point (1 / 2 + x₂) (-5 / 16 + y₂))
      (rotationCoefficients b q hbunit).toFrame)
    (hT : T = placedSquare (point x₃ (11 / 16 + y₃)) identityCoefficients.toFrame)
    (hLi : L ⊆ Circle r) (hRi : R ⊆ Circle r) (hTi : T ⊆ Circle r)
    (hLR : Disjoint L R) (hLT : Disjoint L T) (hRT : Disjoint R T) : False := by
  subst hL hR hT
  have := local_geometry_radius_lower_bound haunit hbunit ha hb hsmall
    ((vertex_inequalities_iff_inside _ _ _).2 hLi) ((vertex_inequalities_iff_inside _ _ _).2 hRi)
    ((vertex_inequalities_iff_inside _ _ _).2 hTi)
    ((coefficient_disjoint_iff_four_axes _ _ _ _).1 hLR)
    ((coefficient_disjoint_iff_four_axes _ _ _ _).1 hLT)
    ((coefficient_disjoint_iff_four_axes _ _ _ _).1 hRT)
  exact absurd hr (not_lt_of_ge this)

theorem rotationCoefficients_eq_identity {a p : ℝ} (h : a ^ 2 + p ^ 2 = 1) (ha : a = 1)
    (hp : p = 0) : rotationCoefficients a p h = identityCoefficients := by
  subst ha hp
  ext <;> simp [rotationCoefficients, identityCoefficients]

namespace CenterElimination

/- ## Ten-variable expressions: rotation variables and centers -/

abbrev E10 := IntervalExpr 10

def lift : IntervalExpr 4 → E10
  | .const q => .const q
  | .var i => .var (Fin.castLE (by norm_num) i)
  | .add e f => .add (lift e) (lift f)
  | .neg e => .neg (lift e)
  | .mul e f => .mul (lift e) (lift f)
  | .square e => .square (lift e)
  | .abs e => .abs (lift e)

theorem lift_eval (e : IntervalExpr 4) (z : Fin 10 → ℝ) :
    (lift e).eval z = e.eval (fun i => z (Fin.castLE (by norm_num) i)) := by
  induction e <;> simp [lift, IntervalExpr.eval, *]

def cvar (i : Fin 3) (k : Fin 2) : E10 := .var ⟨4 + 2 * i.val + k.val, by omega⟩

def symE (g : Fin 8) (e0 e1 : E10) : Fin 2 → E10 :=
  ![![e0, e1], ![.neg e0, e1], ![e0, .neg e1], ![.neg e0, .neg e1],
    ![e1, e0], ![.neg e1, e0], ![e1, .neg e0], ![.neg e1, .neg e0]] g

def signQ : Fin 8 → ℚ := ![1, -1, -1, 1, -1, 1, 1, -1]

theorem signQ_cast (g : Fin 8) : ((signQ g : ℚ) : ℝ) = symmetrySign g := by
  fin_cases g <;> norm_num [signQ, symmetrySign]

def turnAE (k : Fin 4) (a p : E10) : E10 := ![a, .neg p, .neg a, p] k
def turnPE (k : Fin 4) (a p : E10) : E10 := ![p, a, .neg p, .neg a] k

theorem turnE_eval (k : Fin 4) (a p : E10) (z : Fin 10 → ℝ) :
    (turnAE k a p).eval z = turnA k (a.eval z) (p.eval z) ∧
      (turnPE k a p).eval z = turnP k (a.eval z) (p.eval z) := by
  fin_cases k <;> simp [turnAE, turnPE, turnA, turnP, IntervalExpr.eval]

theorem symE_eval (g : Fin 8) (e0 e1 : E10) (z : Fin 10 → ℝ) (k : Fin 2) :
    (symE g e0 e1 k).eval z = planeSymmetry g (point (e0.eval z) (e1.eval z)) k := by
  fin_cases g <;> fin_cases k <;> simp [symE, planeSymmetry, point, IntervalExpr.eval]

/-- Data placing a residual box in the coordinates of the local lemma. -/
structure LocalCert where
  l : Fin 3 → Fin 4 → ℕ
  m : Fin 3 → ℕ
  rho : Fin 3 → ℚ
  top : Fin 3
  left : Fin 3
  right : Fin 3
  g : Fin 8
  turnL : Fin 4
  turnR : Fin 4

namespace LocalCert

variable (D : LocalCert)

def uE : E10 := lift (cosE D.top)
def vE : E10 := lift (sinE D.top)

/-- Center `i` after the inverse rotation of the top frame and the symmetry. -/
def centerE (i : Fin 3) : Fin 2 → E10 :=
  symE D.g (.add (.mul D.uE (cvar i 0)) (.mul D.vE (cvar i 1)))
    (.add (.mul (.neg D.vE) (cvar i 0)) (.mul D.uE (cvar i 1)))

def aE (i : Fin 3) : E10 := .add (.mul D.uE (lift (cosE i))) (.mul D.vE (lift (sinE i)))
def pE (i : Fin 3) : E10 :=
  .mul (.const (signQ D.g))
    (.add (.mul D.uE (lift (sinE i))) (.neg (.mul D.vE (lift (cosE i)))))

def frameA (i : Fin 3) (k : Fin 4) : E10 := turnAE k (D.aE i) (D.pE i)
def frameP (i : Fin 3) (k : Fin 4) : E10 := turnPE k (D.aE i) (D.pE i)

def within (I : RationalInterval) (target : ℚ) : Bool :=
  decide (target - 1 / 64 ≤ I.lo) && decide (I.hi ≤ target + 1 / 64)

def centerBox (C : Certificate) (X : RationalBox 4) (rho : Fin 3 → ℚ) (i : Fin 3) (k : Fin 2) :
    RationalInterval :=
  let r := (if k = 0 then C.residualXg i else C.residualYg i).enclose X
  ⟨-(C.invWeight i) * r.hi - rho i, -(C.invWeight i) * r.lo + rho i⟩

def box10 (X : RationalBox 4) (cb : Fin 3 → Fin 2 → RationalInterval) : RationalBox 10 :=
  ![X 0, X 1, X 2, X 3, cb 0 0, cb 0 1, cb 1 0, cb 1 1, cb 2 0, cb 2 1]

/-- `425/256` minus the second-order lower bound, evaluated by finite
differences. -/
def slack (C : Certificate) (X : RationalBox 4) (region : ℤ) : ℚ :=
  let mid := Quad.midpoint X
  let D := fdData (fun p => evalQ p (C.lowerQE (fun e => widthSign region mid e (C.axis e)))) mid
  425 / 256 - fdLower D (shiftLin region D.g) mid (Quad.radius X)

theorem slack_eq (C : Certificate) (X : RationalBox 4) (region : ℤ) :
    slack C X region = 425 / 256 -
      (Quad.add (C.lowerQuad (fun e => widthSign region (Quad.midpoint X) e (C.axis e)))
        (Certificate.shift region
          (C.lowerQuad (fun e => widthSign region (Quad.midpoint X) e (C.axis e)))
          (Quad.midpoint X))).lower X := by
  unfold slack
  set σ : Fin 3 → ℚ := fun e => widthSign region (Quad.midpoint X) e (C.axis e)
  have hf : (fun p => evalQ p (C.lowerQE σ)) = (C.lowerQuad σ).value := by
    funext p
    have h1 := evalQ_cast (C.lowerQE σ) p
    rw [lowerQE_eval, ← Quad.value_cast] at h1
    exact_mod_cast h1
  simp only []
  rw [hf, fdData_g, fdLower_quad, lower_add_shift]

def check (code : ℕ) (B : TBox) (region : ℤ) : Bool :=
  let C := mkCert code D.l D.m
  let X := rotationBox B.a1 B.b1 B.a2 B.b2
  let δ := slack C X region
  let Z := box10 X (centerBox C X D.rho)
  C.wellFormed &&
  decide (D.top ≠ D.left ∧ D.top ≠ D.right ∧ D.left ≠ D.right) &&
  (List.finRange 3).all (fun i =>
    decide (0 ≤ D.rho i) && decide (δ * C.invWeight i ≤ D.rho i ^ 2)) &&
  within ((D.centerE D.top 0).enclose Z) 0 && within ((D.centerE D.top 1).enclose Z) (11 / 16) &&
  within ((D.centerE D.left 0).enclose Z) (-1 / 2) &&
  within ((D.centerE D.left 1).enclose Z) (-5 / 16) &&
  within ((D.centerE D.right 0).enclose Z) (1 / 2) &&
  within ((D.centerE D.right 1).enclose Z) (-5 / 16) &&
  decide (0 ≤ ((D.frameA D.left D.turnL).enclose Z).lo) &&
  within ((D.frameP D.left D.turnL).enclose Z) 0 &&
  decide (0 ≤ ((D.frameA D.right D.turnR).enclose Z).lo) &&
  within ((D.frameP D.right D.turnR).enclose Z) 0

theorem within_sound {I : RationalInterval} {target : ℚ} {v : ℝ}
    (h : within I target = true) (hv : I.Contains v) : |v - target| ≤ 1 / 64 := by
  simp only [within, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : ((target - 1 / 64 : ℚ) : ℝ) ≤ I.lo := by exact_mod_cast h.1
  have h2 : (I.hi : ℝ) ≤ ((target + 1 / 64 : ℚ) : ℝ) := by exact_mod_cast h.2
  push_cast at h1 h2
  rw [abs_le]; constructor <;> linarith [hv.1, hv.2]

end LocalCert

/-- The quadratic check bounds the raw center-eliminated value from below. -/
theorem slack_bound (C : Certificate) (hwf : C.wellFormed = true) {a1 b1 a2 b2 : ℚ}
    (region : ℤ) (hregion : region = -1 ∨ region = 0 ∨ region = 1)
    (P : SubcriticalRationalRotationPacking 3) (hreg : RegionHolds region (P.t 1) (P.t 2))
    (ha1 : 0 ≤ (a1 : ℝ)) (ht1 : (a1 : ℝ) ≤ P.t 1 ∧ P.t 1 ≤ b1) (hb1 : (b1 : ℝ) ≤ 1)
    (ha2 : 0 ≤ (a2 : ℝ)) (ht2 : (a2 : ℝ) ≤ P.t 2 ∧ P.t 2 ≤ b2) (hb2 : (b2 : ℝ) ≤ 1) :
    425 / 256 - (LocalCert.slack C (rotationBox a1 b1 a2 b2) region : ℝ) ≤
      C.lowerBoundRaw.eval (rotationVector (P.t 1) (P.t 2)) := by
  set x := rotationVector (P.t 1) (P.t 2)
  set B := rotationBox a1 b1 a2 b2
  have hxbox : B.Contains x := rotationVector_mem ha1 ht1 hb1 ha2 ht2 hb2
  set mid := Quad.midpoint B
  set σ : Fin 3 → ℚ := fun e => widthSign region mid e (C.axis e)
  have hσ (e : Fin 3) : σ e = 1 ∨ σ e = -1 ∨ σ e = 0 := by
    rcases widthSign_cases region mid e (C.axis e) with h | h | h | h | h <;>
      rcases hregion with rfl | rfl | rfl <;> simp_all [σ]
  have hL := lowerQuad_le C hwf x σ hσ
  have heq := lowerBound_eval C x
    (by simpa [x, rotationVector] using rational_rotation_unit (P.t 1))
    (by simpa [x, rotationVector] using rational_rotation_unit (P.t 2))
  have hsh := shift_nonpos region (C.lowerQuad σ) mid (P.t_nonneg 1) (P.t_le_one 1)
    (P.t_nonneg 2) (P.t_le_one 2) hreg
  have hq := Quad.lower_le (Quad.add (C.lowerQuad σ) (Certificate.shift region
    (C.lowerQuad σ) mid)) hxbox
  rw [Quad.eval_add] at hq
  rw [LocalCert.slack_eq]
  push_cast
  linarith

/-- The completed squares place every center in the checked center box. -/
theorem center_in_box (C : Certificate) (hwf : C.wellFormed = true) (rho : Fin 3 → ℚ)
    {X : RationalBox 4} (_region : ℤ) (δ : ℚ)
    (hrho : ∀ i, 0 ≤ rho i ∧ δ * C.invWeight i ≤ rho i ^ 2)
    (x : Fin 4 → ℝ) (hx : X.Contains x) (c : Fin 3 → Plane)
    (hdisp : C.lowerBoundRaw.eval x + ∑ i, (C.invWeight i : ℝ) *
      (((C.weight i : ℝ) * c i 0 + (C.residualX i).eval x) ^ 2 +
        ((C.weight i : ℝ) * c i 1 + (C.residualY i).eval x) ^ 2) ≤ 425 / 256)
    (hslack : 425 / 256 - (δ : ℝ) ≤ C.lowerBoundRaw.eval x) (i : Fin 3) (k : Fin 2) :
    (LocalCert.centerBox C X rho i k).Contains (c i k) := by
  have h : (∀ i : Fin 3, (((∀ k : Fin 4, 0 ≤ C.lam i k) ∧ 0 ≤ C.mu i) ∧ 0 ≤ C.invWeight i) ∧
      C.invWeight i * C.weight i = 1) ∧ C.weight 0 + C.weight 1 + C.weight 2 = 1 := by
    simpa [Certificate.wellFormed, List.all_eq_true] using hwf
  have hiw (j : Fin 3) : (0 : ℝ) ≤ C.invWeight j := by exact_mod_cast (h.1 j).1.2
  have hww (j : Fin 3) : (C.invWeight j : ℝ) * C.weight j = 1 := by exact_mod_cast (h.1 j).2
  -- each completed square is at most the slack
  have hterm (j : Fin 3) : 0 ≤ (C.invWeight j : ℝ) *
      (((C.weight j : ℝ) * c j 0 + (C.residualX j).eval x) ^ 2 +
        ((C.weight j : ℝ) * c j 1 + (C.residualY j).eval x) ^ 2) :=
    mul_nonneg (hiw j) (by positivity)
  have hsum : (C.invWeight i : ℝ) *
      (((C.weight i : ℝ) * c i 0 + (C.residualX i).eval x) ^ 2 +
        ((C.weight i : ℝ) * c i 1 + (C.residualY i).eval x) ^ 2) ≤ δ := by
    simp only [Fin.sum_univ_three] at hdisp
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      linarith [hterm 0, hterm 1, hterm 2]
  set r := (if k = 0 then C.residualX i else C.residualY i).eval x with hr
  have hsq : (C.invWeight i : ℝ) * ((C.weight i : ℝ) * c i k + r) ^ 2 ≤ δ := by
    have hk : ((C.weight i : ℝ) * c i k + r) ^ 2 ≤
        ((C.weight i : ℝ) * c i 0 + (C.residualX i).eval x) ^ 2 +
          ((C.weight i : ℝ) * c i 1 + (C.residualY i).eval x) ^ 2 := by
      fin_cases k <;> simp [r] <;> nlinarith [sq_nonneg ((C.weight i : ℝ) * c i 1 +
        (C.residualY i).eval x), sq_nonneg ((C.weight i : ℝ) * c i 0 + (C.residualX i).eval x)]
    nlinarith [mul_le_mul_of_nonneg_left hk (hiw i)]
  -- (w c + r)² iw = w (c + iw r)²
  have hdev : (c i k + C.invWeight i * r) ^ 2 ≤ (rho i : ℝ) ^ 2 := by
    have e1 : (C.invWeight i : ℝ) * ((C.weight i : ℝ) * c i k + r) ^ 2 =
        C.weight i * (c i k + C.invWeight i * r) ^ 2 := by
      linear_combination ((C.weight i : ℝ) * c i k ^ 2 - C.invWeight i * r ^ 2) * hww i
    have h2 : (C.weight i : ℝ) * (c i k + C.invWeight i * r) ^ 2 ≤ δ := by
      rw [← e1]; exact hsq
    have h3 := mul_le_mul_of_nonneg_left h2 (hiw i)
    have h4 : (C.invWeight i : ℝ) * ((C.weight i : ℝ) * (c i k + C.invWeight i * r) ^ 2) =
        (c i k + C.invWeight i * r) ^ 2 := by
      rw [← mul_assoc, hww i, one_mul]
    have hδ : ((δ * C.invWeight i : ℚ) : ℝ) ≤ ((rho i ^ 2 : ℚ) : ℝ) := by
      exact_mod_cast (hrho i).2
    push_cast at hδ
    linarith
  have hdev' : |c i k + C.invWeight i * r| ≤ rho i := by
    have hr0 : (0 : ℝ) ≤ rho i := by exact_mod_cast (hrho i).1
    exact abs_le_of_sq_le_sq' hdev hr0 |> fun h => abs_le.mpr ⟨h.1, h.2⟩
  -- enclosure of the residual
  have hrg : ((if k = 0 then C.residualXg i else C.residualYg i).enclose X).Contains r := by
    have := (if k = 0 then C.residualXg i else C.residualYg i).enclose_contains hx
    fin_cases k <;> simpa [r, (residualXg_eval C x i).1, (residualXg_eval C x i).2] using this
  obtain ⟨hlo, hhi⟩ := hrg
  obtain ⟨d1, d2⟩ := abs_le.mp hdev'
  simp only [LocalCert.centerBox, RationalInterval.Contains]
  push_cast
  constructor <;> nlinarith [hiw i]

/-- The image of a rationally rotated placed square under the inverse top
rotation, a square symmetry and `k` internal quarter turns. -/
theorem image_placed (g : Fin 8) (k : Fin 4) {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1)
    (c : Plane) (t : ℝ) :
    (fun w => planeSymmetry g (rotInv u v w)) ''
        placedSquare c (rationalRotationCoefficients t).toFrame =
      placedSquare (planeSymmetry g (rotInv u v c))
        (rotationCoefficients
          (turnA k (u * rationalCos t + v * rationalSin t)
            (symmetrySign g * (u * rationalSin t - v * rationalCos t)))
          (turnP k (u * rationalCos t + v * rationalSin t)
            (symmetrySign g * (u * rationalSin t - v * rationalCos t)))
          (turn_unit k (symmetric_unit g
            (rotation_difference_unit huv (rational_rotation_unit t))))).toFrame := by
  rw [← placedSquare_turn k _ (symmetric_unit g
    (rotation_difference_unit huv (rational_rotation_unit t))), ← Set.image_image]
  unfold rationalRotationCoefficients
  rw [← placedSquare_rotInv huv (rational_rotation_unit t) c,
    ← placedSquare_symmetry g _ (rotation_difference_unit huv (rational_rotation_unit t))]

theorem LocalCert.excludes (D : LocalCert) (code : ℕ) (B : TBox) (region : ℤ)
    (hcheck : D.check code B region = true) {r : ℝ≥0} (P : RationalRotationPacking 3 r)
    (hr : r < radius) (h0 : P.t 0 = 0) (hreal : Realizes (P.toSubcritical hr) code)
    (hB : B.Inside) (ht : B.Contains (P.t 1) (P.t 2)) (hvr : QTree.ValidRegion region)
    (hreg : RegionHolds region (P.t 1) (P.t 2)) : False := by
  set Q := P.toSubcritical hr
  set C := mkCert code D.l D.m
  set X := rotationBox B.a1 B.b1 B.a2 B.b2
  set δ := LocalCert.slack C X region
  set Z := LocalCert.box10 X (LocalCert.centerBox C X D.rho)
  have hc : C.wellFormed = true ∧ (D.top ≠ D.left ∧ D.top ≠ D.right ∧ D.left ≠ D.right) ∧
      (∀ i ∈ List.finRange 3, (decide (0 ≤ D.rho i) && decide (δ * C.invWeight i ≤ D.rho i ^ 2))
        = true) ∧
      LocalCert.within ((D.centerE D.top 0).enclose Z) 0 = true ∧
      LocalCert.within ((D.centerE D.top 1).enclose Z) (11 / 16) = true ∧
      LocalCert.within ((D.centerE D.left 0).enclose Z) (-1 / 2) = true ∧
      LocalCert.within ((D.centerE D.left 1).enclose Z) (-5 / 16) = true ∧
      LocalCert.within ((D.centerE D.right 0).enclose Z) (1 / 2) = true ∧
      LocalCert.within ((D.centerE D.right 1).enclose Z) (-5 / 16) = true ∧
      0 ≤ ((D.frameA D.left D.turnL).enclose Z).lo ∧
      LocalCert.within ((D.frameP D.left D.turnL).enclose Z) 0 = true ∧
      0 ≤ ((D.frameA D.right D.turnR).enclose Z).lo ∧
      LocalCert.within ((D.frameP D.right D.turnR).enclose Z) 0 = true := by
    simpa [LocalCert.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]
      using hcheck
  obtain ⟨hwf, hroles, hrhos, hT0, hT1, hL0, hL1, hR0, hR1, hLa, hLp, hRa, hRp⟩ := hc
  have hrho (i : Fin 3) : 0 ≤ D.rho i ∧ δ * C.invWeight i ≤ D.rho i ^ 2 := by
    simpa using hrhos i (List.mem_finRange i)
  obtain ⟨h1, h2, h3, h4⟩ := hB
  have ha1 : 0 ≤ (B.a1 : ℝ) := by exact_mod_cast h1
  have hb1 : (B.b1 : ℝ) ≤ 1 := by exact_mod_cast h2
  have ha2 : 0 ≤ (B.a2 : ℝ) := by exact_mod_cast h3
  have hb2 : (B.b2 : ℝ) ≤ 1 := by exact_mod_cast h4
  set x := rotationVector (P.t 1) (P.t 2)
  have hx : X.Contains x := rotationVector_mem ha1 ⟨ht.1, ht.2.1⟩ hb1 ha2 ⟨ht.2.2.1, ht.2.2.2⟩ hb2
  have hu1 : x 0 ^ 2 + x 1 ^ 2 = 1 := by
    simpa [x, rotationVector] using rational_rotation_unit (P.t 1)
  have hu2 : x 2 ^ 2 + x 3 ^ 2 = 1 := by
    simpa [x, rotationVector] using rational_rotation_unit (P.t 2)
  have hslack := slack_bound C hwf region hvr Q hreg ha1 ⟨ht.1, ht.2.1⟩ hb1 ha2
    ⟨ht.2.2.1, ht.2.2.2⟩ hb2
  have hdisp := lowerBoundRaw_disp C hwf x hu1 hu2 P.centers
    (by
      intro i k
      have hv : StrictCandidateVertexInequalities (P.centers i)
          (rationalRotationCoefficients (P.t i)) := Q.vertices i
      have hr : cosR x i = rationalCos (P.t i) ∧ sinR x i = rationalSin (P.t i) :=
        cosR_rotation Q h0 i
      unfold StrictCandidateVertexInequalities at hv
      simp only [vertexSquared_rational] at hv
      unfold VertexBound
      rw [hr.1, hr.2]
      fin_cases k <;> simp only [cornerX_0, cornerX_1, cornerX_2, cornerX_3, cornerY_0,
        cornerY_1, cornerY_2, cornerY_3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        push_cast <;> linarith [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2])
    (fun e => hreal e)
  set c := P.centers
  have hcb := center_in_box C hwf D.rho region δ hrho x hx c hdisp hslack
  set z : Fin 10 → ℝ := ![x 0, x 1, x 2, x 3, c 0 0, c 0 1, c 1 0, c 1 1, c 2 0, c 2 1]
  have hz : Z.Contains z := by
    intro j
    fin_cases j
    · exact hx 0
    · exact hx 1
    · exact hx 2
    · exact hx 3
    · exact hcb 0 0
    · exact hcb 0 1
    · exact hcb 1 0
    · exact hcb 1 1
    · exact hcb 2 0
    · exact hcb 2 1
  have hlift (e : IntervalExpr 4) : (lift e).eval z = e.eval x := by
    rw [lift_eval]
    congr 1
    ext j; fin_cases j <;> rfl
  have hcv (i : Fin 3) (k : Fin 2) : (cvar i k).eval z = c i k := by
    fin_cases i <;> fin_cases k <;> rfl
  have hrot (i : Fin 3) : cosR x i = rationalCos (P.t i) ∧ sinR x i = rationalSin (P.t i) :=
    cosR_rotation Q h0 i
  set u := rationalCos (P.t D.top)
  set v := rationalSin (P.t D.top)
  have huv : u ^ 2 + v ^ 2 = 1 := rational_rotation_unit _
  have hU : D.uE.eval z = u := by
    simp only [LocalCert.uE, hlift]; exact (hrot D.top).1
  have hV : D.vE.eval z = v := by
    simp only [LocalCert.vE, hlift]; exact (hrot D.top).2
  set F : Fin 3 → Plane := fun i => planeSymmetry D.g (rotInv u v (c i))
  have hF (i : Fin 3) (k : Fin 2) : (D.centerE i k).eval z = F i k := by
    simp only [LocalCert.centerE, symE_eval, IntervalExpr.eval, hU, hV, hcv, F, rotInv]
  set aR : Fin 3 → ℝ := fun i => u * rationalCos (P.t i) + v * rationalSin (P.t i)
  set pR : Fin 3 → ℝ := fun i => symmetrySign D.g * (u * rationalSin (P.t i) - v * rationalCos (P.t i))
  have hA (i : Fin 3) (k : Fin 4) :
      (D.frameA i k).eval z = turnA k (aR i) (pR i) ∧
        (D.frameP i k).eval z = turnP k (aR i) (pR i) := by
    have he : (D.aE i).eval z = aR i ∧ (D.pE i).eval z = pR i := by
      constructor
      · simp only [LocalCert.aE, IntervalExpr.eval, hU, hV, hlift, aR]
        rw [show IntervalExpr.eval x (cosE i) = cosR x i from rfl,
          show IntervalExpr.eval x (sinE i) = sinR x i from rfl, (hrot i).1, (hrot i).2]
      · simp only [LocalCert.pE, IntervalExpr.eval, hU, hV, hlift, pR, signQ_cast]
        rw [show IntervalExpr.eval x (cosE i) = cosR x i from rfl,
          show IntervalExpr.eval x (sinE i) = sinR x i from rfl, (hrot i).1, (hrot i).2]
        ring
    simp only [LocalCert.frameA, LocalCert.frameP, (turnE_eval k _ _ z).1,
      (turnE_eval k _ _ z).2, he.1, he.2]
    simp
  -- numeric bounds from the enclosures
  have bnd (e : E10) {tgt : ℚ} (h : LocalCert.within (e.enclose Z) tgt = true) :
      |e.eval z - tgt| ≤ 1 / 64 := LocalCert.within_sound h (e.enclose_contains hz)
  have bT0 := bnd _ hT0
  have bT1 := bnd _ hT1
  have bL0 := bnd _ hL0
  have bL1 := bnd _ hL1
  have bR0 := bnd _ hR0
  have bR1 := bnd _ hR1
  have bLp := bnd _ hLp
  have bRp := bnd _ hRp
  rw [hF] at bT0 bT1 bL0 bL1 bR0 bR1
  rw [(hA _ _).2] at bLp bRp
  have aL : 0 ≤ turnA D.turnL (aR D.left) (pR D.left) := by
    have := ((D.frameA D.left D.turnL).enclose_contains hz).1
    rw [(hA _ _).1] at this
    exact le_trans (by exact_mod_cast hLa) this
  have aRt : 0 ≤ turnA D.turnR (aR D.right) (pR D.right) := by
    have := ((D.frameA D.right D.turnR).enclose_contains hz).1
    rw [(hA _ _).1] at this
    exact le_trans (by exact_mod_cast hRa) this
  -- the placed squares and their images
  let Sq : Fin 3 → Set Plane := fun i =>
    placedSquare (c i) (rationalRotationCoefficients (P.t i)).toFrame
  have hin (i : Fin 3) : Sq i ⊆ Circle r := (vertex_inequalities_iff_inside _ _ _).1 (P.vertices i)
  have hdis (i j : Fin 3) (hij : i ≠ j) : Disjoint (Sq i) (Sq j) := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact (coefficient_disjoint_iff_four_axes _ _ _ _).2 (P.separations i j h)
    · exact ((coefficient_disjoint_iff_four_axes _ _ _ _).2 (P.separations j i h)).symm
  set M : Plane → Plane := fun w => planeSymmetry D.g (rotInv u v w)
  have hMinj : Function.Injective M :=
    (planeSymmetry_injective D.g).comp (rotInv_injective huv)
  have hMin (i : Fin 3) : M '' Sq i ⊆ Circle r := by
    rintro _ ⟨w, hw, rfl⟩
    exact (planeSymmetry_mem_circle_iff D.g r _).2 ((rotInv_mem_circle_iff huv r w).2 (hin i hw))
  have hMdis (i j : Fin 3) (hij : i ≠ j) : Disjoint (M '' Sq i) (M '' Sq j) :=
    (Set.disjoint_image_iff hMinj).2 (hdis i j hij)
  have hpt (w : Plane) (a b : ℝ) : point (a + (w 0 - a)) (b + (w 1 - b)) = w := by
    ext k; fin_cases k <;> simp [point]
  -- the top square becomes axis-parallel
  have htopframe : aR D.top = 1 ∧ pR D.top = 0 := by
    constructor
    · simp only [aR]; nlinarith [huv]
    · simp only [pR]; ring
  have hTimg : M '' Sq D.top = placedSquare (point (F D.top 0) (11 / 16 + (F D.top 1 - 11 / 16)))
      identityCoefficients.toFrame := by
    rw [image_placed D.g 0 huv (c D.top) (P.t D.top)]
    congr 1
    · ext k; fin_cases k <;> simp [point, F]
    · rw [rotationCoefficients_eq_identity]
      · simpa [turnA] using htopframe.1
      · have := htopframe.2
        simp only [turnP, Matrix.cons_val_zero]
        exact this
  have hLimg := image_placed D.g D.turnL huv (c D.left) (P.t D.left)
  have hRimg := image_placed D.g D.turnR huv (c D.right) (P.t D.right)
  refine local_sets_lower_bound hr (x₁ := F D.left 0 - -1 / 2) (y₁ := F D.left 1 - -5 / 16)
    (x₂ := F D.right 0 - 1 / 2) (y₂ := F D.right 1 - -5 / 16) (x₃ := F D.top 0)
    (y₃ := F D.top 1 - 11 / 16) (a := turnA D.turnL (aR D.left) (pR D.left))
    (p := turnP D.turnL (aR D.left) (pR D.left))
    (b := turnA D.turnR (aR D.right) (pR D.right))
    (q := turnP D.turnR (aR D.right) (pR D.right))
    (turn_unit D.turnL (symmetric_unit D.g
      (rotation_difference_unit huv (rational_rotation_unit (P.t D.left)))))
    (turn_unit D.turnR (symmetric_unit D.g
      (rotation_difference_unit huv (rational_rotation_unit (P.t D.right))))) aL aRt ?_ (M '' Sq D.left) (M '' Sq D.right)
    (M '' Sq D.top) ?_ ?_ hTimg (hMin _) (hMin _) (hMin _)
    (hMdis _ _ hroles.2.2) (hMdis _ _ (Ne.symm hroles.1)) (hMdis _ _ (Ne.symm hroles.2.1))
  · simp only [perturbation]
    push_cast at bT0 bT1 bL0 bL1 bR0 bR1 bLp bRp
    refine max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_))))))
    · simpa using bL0
    · simpa using bL1
    · simpa using bR0
    · simpa using bR1
    · simpa using bT0
    · simpa using bT1
    · simpa using bLp
    · simpa using bRp
  · rw [hLimg]; congr 1; exact (hpt _ _ _).symm
  · rw [hRimg]; congr 1; exact (hpt _ _ _).symm

end CenterElimination

end

end ThreeSquares
