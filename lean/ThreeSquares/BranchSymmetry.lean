import ThreeSquares.GlobalCertificate

/-! # Reducing the 512 separation branches to 64 representatives

A global quarter turn keeps every rotation parameter and the normalization of
square 0; exchanging squares 1 and 2 swaps the two parameters.  Both act on the
realized separation branch by an explicit map of branch codes.  Every branch
code is moved into a fixed set of 64 representatives, so certificate trees are
needed only for those.
-/

namespace ThreeSquares
namespace CenterElimination

open scoped NNReal
open SquarePacking

noncomputable section

/- ## Branch code maps -/

/-- A quarter turn exchanges the two columns of the owner square. -/
def rotAxis : Fin 4 → Fin 4 := ![1, 0, 3, 2]
def rotSign (a : Fin 4) (s : Bool) : Bool := if a.val % 2 = 0 then s else !s

def rotCode (c : ℕ) : ℕ :=
  encode (fun e => rotAxis (axisOf c e)) (fun e => rotSign (axisOf c e) (signOf c e))

/-- Exchanging squares 1 and 2 exchanges pairs `(0,1)`, `(0,2)` and reverses
pair `(1,2)`. -/
def swapCode (c : ℕ) : ℕ :=
  encode ![axisOf c 1, axisOf c 0, axisOf c 2 + 2] ![signOf c 1, signOf c 0, !signOf c 2]

/- ## Geometric transformations of normalized packings -/

theorem symmetrySign_five : symmetrySign 5 = 1 := by simp [symmetrySign]

theorem rotationCoefficients_sign_five {a p : ℝ} (h : a ^ 2 + p ^ 2 = 1)
    (h' : a ^ 2 + (symmetrySign 5 * p) ^ 2 = 1) :
    rotationCoefficients a (symmetrySign 5 * p) h' = rotationCoefficients a p h := by
  ext <;> simp [rotationCoefficients, symmetrySign_five]

/-- The global quarter turn `(x, y) ↦ (-y, x)`. -/
def _root_.ThreeSquares.RationalRotationPacking.rot90 {r : ℝ≥0} (P : RationalRotationPacking 3 r) :
    RationalRotationPacking 3 r where
  centers i := planeSymmetry 5 (P.centers i)
  t := P.t
  t_nonneg := P.t_nonneg
  t_le_one := P.t_le_one
  vertices i := by
    have h := (vertexInequalities_symmetry_iff 5 (P.centers i) (rational_rotation_unit (P.t i))
      (symmetric_unit 5 (rational_rotation_unit (P.t i)))).2 (P.vertices i)
    rwa [rotationCoefficients_sign_five (rational_rotation_unit (P.t i))] at h
  separations i j hij := by
    have h := (fourAxisSeparation_symmetry_iff 5 (P.centers i) (P.centers j)
      (rational_rotation_unit (P.t i)) (rational_rotation_unit (P.t j))
      (symmetric_unit 5 (rational_rotation_unit (P.t i)))
      (symmetric_unit 5 (rational_rotation_unit (P.t j)))).2 (P.separations i j hij)
    rwa [rotationCoefficients_sign_five (rational_rotation_unit (P.t i)),
      rotationCoefficients_sign_five (rational_rotation_unit (P.t j))] at h

def swapLabel : Fin 3 → Fin 3 := ![0, 2, 1]

theorem fourAxisSeparation_symm (c d : Plane) (A B : OrthogonalCoefficients)
    (h : FourAxisSeparation c d A B) : FourAxisSeparation d c B A :=
  (coefficient_disjoint_iff_four_axes _ _ _ _).1
    ((coefficient_disjoint_iff_four_axes _ _ _ _).2 h).symm

/-- Exchange of the labels of squares 1 and 2. -/
def _root_.ThreeSquares.RationalRotationPacking.swap12 {r : ℝ≥0} (P : RationalRotationPacking 3 r) :
    RationalRotationPacking 3 r where
  centers i := P.centers (swapLabel i)
  t i := P.t (swapLabel i)
  t_nonneg i := P.t_nonneg _
  t_le_one i := P.t_le_one _
  vertices i := P.vertices _
  separations i j hij := by
    fin_cases i <;> fin_cases j <;> simp at hij
    · exact P.separations 0 2 (by decide)
    · exact P.separations 0 1 (by decide)
    · exact fourAxisSeparation_symm _ _ _ _ (P.separations 1 2 (by decide))

theorem _root_.ThreeSquares.RationalRotationPacking.rot90_t {r : ℝ≥0} (P : RationalRotationPacking 3 r) :
    P.rot90.t = P.t := rfl

theorem _root_.ThreeSquares.RationalRotationPacking.swap12_t {r : ℝ≥0} (P : RationalRotationPacking 3 r) (i : Fin 3) :
    P.swap12.t i = P.t (swapLabel i) := rfl

/- ## Transfer of the realized branch -/

/-- The projected half-width sum is invariant under exchanging an axis `(u, v)`
with `ε (-v, u)`. -/
theorem width_quarter (u v c s ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    |ε * -v * c + ε * u * s| + |-(ε * -v * s) + ε * u * c| =
      |u * c + v * s| + |-(u * s) + v * c| := by
  rcases hε with rfl | rfl
  · rw [show (1 : ℝ) * -v * c + 1 * u * s = -(-(u * s) + v * c) by ring, abs_neg,
      show -((1 : ℝ) * -v * s) + 1 * u * c = u * c + v * s by ring]
    ring
  · rw [show (-1 : ℝ) * -v * c + -1 * u * s = -(u * s) + v * c by ring,
      show -((-1 : ℝ) * -v * s) + -1 * u * c = -(u * c + v * s) by ring, abs_neg]
    ring

theorem rot_axis_eval (x : Fin 4 → ℝ) (e : Fin 3) (a : Fin 4) :
    let ε : ℝ := if a.val % 2 = 0 then 1 else -1
    (axisU e (rotAxis a)).eval x = ε * -(axisV e a).eval x ∧
      (axisV e (rotAxis a)).eval x = ε * (axisU e a).eval x := by
  fin_cases a <;> simp [rotAxis, axisU, axisV, IntervalExpr.eval]

/-- Signed separation value along axis `a` of pair `e`. -/
def Xv (a : Fin 4) (x : Fin 4 → ℝ) (cc : Fin 3 → Plane) (e : Fin 3) : ℝ :=
  (axisU e a).eval x * (cc (pairSnd e) 0 - cc (pairFst e) 0) +
    (axisV e a).eval x * (cc (pairSnd e) 1 - cc (pairFst e) 1)

def SepHolds (a : Fin 4) (s : Bool) (x : Fin 4 → ℝ) (cc : Fin 3 → Plane) (e : Fin 3) : Prop :=
  (halfWidthE e a).eval x ≤ if s then Xv a x cc e else -Xv a x cc e

theorem realizes_iff (Q : SubcriticalRationalRotationPacking 3) (code : ℕ) :
    Realizes Q code ↔ ∀ e, SepHolds (axisOf code e) (signOf code e)
      (rotationVector (Q.t 1) (Q.t 2)) Q.centers e := Iff.rfl

theorem halfWidth_rot (x : Fin 4 → ℝ) (e : Fin 3) (a : Fin 4) :
    (halfWidthE e (rotAxis a)).eval x = (halfWidthE e a).eval x := by
  obtain ⟨hu, hv⟩ := rot_axis_eval x e a
  have hε : (if a.val % 2 = 0 then (1 : ℝ) else -1) = 1 ∨
      (if a.val % 2 = 0 then (1 : ℝ) else -1) = -1 := by
    split_ifs <;> simp
  simp only [halfWidthE, widthE, IntervalExpr.eval, hu, hv]
  rw [width_quarter _ _ _ _ _ hε, width_quarter _ _ _ _ _ hε]

theorem Xv_rot (x : Fin 4 → ℝ) (cc : Fin 3 → Plane) (e : Fin 3) (a : Fin 4) :
    Xv (rotAxis a) x (fun i => planeSymmetry 5 (cc i)) e =
      (if a.val % 2 = 0 then (1 : ℝ) else -1) * Xv a x cc e := by
  obtain ⟨hu, hv⟩ := rot_axis_eval x e a
  simp only [Xv, hu, hv, planeSymmetry, point, Matrix.cons_val, Fin.isValue]
  split_ifs <;> simp <;> ring

theorem sepHolds_rot (x : Fin 4 → ℝ) (cc : Fin 3 → Plane) (e : Fin 3) (a : Fin 4) (s : Bool)
    (h : SepHolds a s x cc e) :
    SepHolds (rotAxis a) (rotSign a s) x (fun i => planeSymmetry 5 (cc i)) e := by
  unfold SepHolds at h ⊢
  rw [halfWidth_rot, Xv_rot]
  unfold rotSign
  by_cases hcol : a.val % 2 = 0 <;> simp only [hcol, if_true, if_false] <;>
    cases s <;> simpa using h

theorem realizes_rot90 {r : ℝ≥0} (P : RationalRotationPacking 3 r) (hr : r < radius)
    (c : ℕ) (h : Realizes (P.toSubcritical hr) c) :
    Realizes (P.rot90.toSubcritical hr) (rotCode c) := by
  rw [realizes_iff] at h ⊢
  intro e
  have hax : axisOf (rotCode c) e = rotAxis (axisOf c e) := congrFun (decode_encode _ _).1 e
  have hsg : signOf (rotCode c) e = rotSign (axisOf c e) (signOf c e) :=
    congrFun (decode_encode _ _).2 e
  rw [hax, hsg]
  exact sepHolds_rot _ _ e _ _ (h e)

/- ## Transfer through the exchange of squares 1 and 2 -/

def swapVars (x : Fin 4 → ℝ) : Fin 4 → ℝ := ![x 2, x 3, x 0, x 1]

theorem swap_rotationVector (t1 t2 : ℝ) :
    rotationVector t2 t1 = swapVars (rotationVector t1 t2) := by
  ext j; fin_cases j <;> rfl

theorem swap_pair01 (x : Fin 4 → ℝ) (cc : Fin 3 → Plane) (a : Fin 4) (s : Bool)
    (h : SepHolds a s x cc 1) :
    SepHolds a s (swapVars x) (fun i => cc (swapLabel i)) 0 := by
  unfold SepHolds Xv at h ⊢
  fin_cases a <;>
    simpa [halfWidthE, widthE, axisU, axisV, cosE, sinE, pairFst, pairSnd, swapVars,
      swapLabel, IntervalExpr.eval] using h

theorem swap_pair02 (x : Fin 4 → ℝ) (cc : Fin 3 → Plane) (a : Fin 4) (s : Bool)
    (h : SepHolds a s x cc 0) :
    SepHolds a s (swapVars x) (fun i => cc (swapLabel i)) 1 := by
  unfold SepHolds Xv at h ⊢
  fin_cases a <;>
    simpa [halfWidthE, widthE, axisU, axisV, cosE, sinE, pairFst, pairSnd, swapVars,
      swapLabel, IntervalExpr.eval] using h

theorem swap_pair12 (x : Fin 4 → ℝ) (cc : Fin 3 → Plane) (a : Fin 4) (s : Bool)
    (h : SepHolds a s x cc 2) :
    SepHolds (a + 2) (!s) (swapVars x) (fun i => cc (swapLabel i)) 2 := by
  unfold SepHolds Xv at h ⊢
  fin_cases a <;> cases s <;>
    simp [halfWidthE, widthE, axisU, axisV, cosE, sinE, pairFst, pairSnd, swapVars,
      swapLabel, IntervalExpr.eval] at h ⊢ <;>
    linarith [h]

theorem realizes_swap12 {r : ℝ≥0} (P : RationalRotationPacking 3 r) (hr : r < radius)
    (c : ℕ) (h : Realizes (P.toSubcritical hr) c) :
    Realizes (P.swap12.toSubcritical hr) (swapCode c) := by
  rw [realizes_iff] at h ⊢
  have hax : axisOf (swapCode c) = ![axisOf c 1, axisOf c 0, axisOf c 2 + 2] :=
    (decode_encode _ _).1
  have hsg : signOf (swapCode c) = ![signOf c 1, signOf c 0, !signOf c 2] :=
    (decode_encode _ _).2
  have hx : rotationVector ((P.swap12.toSubcritical hr).t 1) ((P.swap12.toSubcritical hr).t 2) =
      swapVars (rotationVector ((P.toSubcritical hr).t 1) ((P.toSubcritical hr).t 2)) :=
    swap_rotationVector _ _
  have hc : (P.swap12.toSubcritical hr).centers =
      fun i => (P.toSubcritical hr).centers (swapLabel i) := rfl
  intro e
  rw [hax, hsg, hx, hc]
  fin_cases e
  · exact swap_pair01 _ _ _ _ (h 1)
  · exact swap_pair02 _ _ _ _ (h 0)
  · exact swap_pair12 _ _ _ _ (h 2)

/- ## Symmetry words and the reduced global theorem -/

def applyCode (k : ℕ) (b : Bool) (c : ℕ) : ℕ := rotCode^[k] (if b then swapCode c else c)

def applyPacking {r : ℝ≥0} (k : ℕ) (b : Bool) (P : RationalRotationPacking 3 r) :
    RationalRotationPacking 3 r :=
  RationalRotationPacking.rot90^[k] (if b then P.swap12 else P)

theorem applyPacking_t0 {r : ℝ≥0} (k : ℕ) (b : Bool) (P : RationalRotationPacking 3 r) :
    (applyPacking k b P).t 0 = P.t 0 := by
  unfold applyPacking
  induction k with
  | zero => cases b <;> rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih

theorem realizes_apply {r : ℝ≥0} (P : RationalRotationPacking 3 r) (hr : r < radius)
    (k : ℕ) (b : Bool) (c : ℕ) (h : Realizes (P.toSubcritical hr) c) :
    Realizes ((applyPacking k b P).toSubcritical hr) (applyCode k b c) := by
  unfold applyPacking applyCode
  induction k with
  | zero =>
    cases b
    · exact h
    · exact realizes_swap12 P hr c h
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact realizes_rot90 _ hr _ ih

/-- Checked trees for representatives of all branch orbits prove the
unconditional lower bound. -/
theorem global_lower_bound_of_rep_trees (L : List CodedGTree) (word : ℕ → ℕ × Bool)
    (hword : ∀ c < 512, applyCode (word c).1 (word c).2 c ∈ L.map CodedGTree.code)
    (hcheck : ∀ T ∈ L, T.tree.check T.code TBox.unit 0 = true) : GlobalLowerBound := by
  intro r hfeas
  by_contra hn
  have hr : r < radius := lt_of_not_ge hn
  obtain ⟨P, h0⟩ := (normalized_rational_rotation_packing_iff 3 r 0).mpr hfeas
  obtain ⟨c, hlt, hreal⟩ := exists_realized (P.toSubcritical hr) h0
  set P' := applyPacking (word c).1 (word c).2 P
  have h0' : P'.t 0 = 0 := by rw [applyPacking_t0]; exact h0
  have hreal' := realizes_apply P hr (word c).1 (word c).2 c hreal
  obtain ⟨T, hT, hTc⟩ := List.mem_map.mp (hword c hlt)
  rw [← hTc] at hreal'
  exact T.tree.check_sound T.code TBox.unit 0 (by simp [TBox.Inside, TBox.unit])
    (Or.inr (Or.inl rfl)) (hcheck T hT) P' hr h0' hreal'
    ⟨by simpa [TBox.unit] using P'.t_nonneg 1, by simpa [TBox.unit] using P'.t_le_one 1,
      by simpa [TBox.unit] using P'.t_nonneg 2, by simpa [TBox.unit] using P'.t_le_one 2⟩
    ⟨fun h => absurd h (lt_irrefl 0), fun h => absurd h (lt_irrefl 0)⟩

end

end CenterElimination
end ThreeSquares
