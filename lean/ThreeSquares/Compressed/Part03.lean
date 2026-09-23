import ThreeSquares.Compressed.Domains

/-! Four generated representative exclusions, checked by the kernel. -/


/- Generated compressed exclusion certificate. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSquares.CenterElimination.Compressed.Case040

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 40 ![![0, 0, 0, 19456], ![0, 19456, 0, 0], ![13312, 0, 13312, 0]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (5035 / 16384 : ℚ), (57 / 512 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (7904 : ℚ), (-15808 : ℚ)], ![(-2128 : ℚ), (15808 : ℚ), (5776 : ℚ)], ![(-12939 : ℚ), (0 : ℚ), (-12939 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, 1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri1_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri1.x u v) (tri1.y u v) :=
  triangle_nonnegative_of_coefficients n tri1 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (-1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y ∨ tri1.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    obtain ⟨h,k⟩ := h

    rcases h with h | h | h <;> rcases k with k | k | k

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0, tri1] at *

    all_goals linarith

  rcases hc with hc | hc

  · exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

  · exact tri1.nonneg (by norm_num [tri1, Triangle.det]) n tri1_nonnegative hc

fc_compact_decl theorem excludes : Excludes 40 box (-1) :=

  excludes_of_scaled_numerator 40 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 40 ![![0, 0, 0, 24576], ![0, 16384, 0, 0], ![24576, 0, 0, 0]] ![49152, 49152, 8192]

fc_compact_decl def a : Seven := ![(-17 / 192 : ℚ), (5 / 8 : ℚ), (9 / 16 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-191 : ℚ), (1344 : ℚ), (-1535 : ℚ)], ![(672 : ℚ), (384 : ℚ), (1056 : ℚ)], ![(-1343 : ℚ), (960 : ℚ), (-2303 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, 1]

fc_compact_decl def box : TBox := ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (-1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    rcases h with h | h | h

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0] at *

    all_goals linarith

  exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

fc_compact_decl theorem excludes : Excludes 40 box (-1) :=

  excludes_of_scaled_numerator 40 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 40 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) :=
  excludes_split 40 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) false (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box])

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 40 ![![0, 0, 0, 19456], ![0, 19456, 0, 0], ![13312, 13312, 0, 0]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (5035 / 16384 : ℚ), (57 / 512 : ℚ), (247 / 1024 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (247 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-3952 : ℚ), (15808 : ℚ), (-11856 : ℚ)], ![(-6080 : ℚ), (7904 : ℚ), (9728 : ℚ)], ![(-12939 : ℚ), (0 : ℚ), (-12939 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, 1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri1_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri1.x u v) (tri1.y u v) :=
  triangle_nonnegative_of_coefficients n tri1 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (-1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y ∨ tri1.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    obtain ⟨h,k⟩ := h

    rcases h with h | h | h <;> rcases k with k | k | k

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0, tri1] at *

    all_goals linarith

  rcases hc with hc | hc

  · exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

  · exact tri1.nonneg (by norm_num [tri1, Triangle.det]) n tri1_nonnegative hc

fc_compact_decl theorem excludes : Excludes 40 box (-1) :=

  excludes_of_scaled_numerator 40 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 40 ![![0, 0, 0, 24576], ![0, 20480, 0, 0], ![20480, 0, 0, 0]] ![49152, 45056, 16384]

fc_compact_decl def a : Seven := ![(133 / 1920 : ℚ), (19 / 40 : ℚ), (9 / 20 : ℚ), (11 / 16 : ℚ), (11 / 16 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-685 : ℚ), (7200 : ℚ), (-7885 : ℚ)], ![(1536 : ℚ), (3840 : ℚ), (5376 : ℚ)], ![(-6253 : ℚ), (3360 : ℚ), (-9613 : ℚ)]]

fc_compact_decl def scale : ℚ := 3840

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, 1]

fc_compact_decl def box : TBox := ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri1_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri1.x u v) (tri1.y u v) :=
  triangle_nonnegative_of_coefficients n tri1 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (-1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y ∨ tri1.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    obtain ⟨h,k⟩ := h

    rcases h with h | h | h <;> rcases k with k | k | k

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0, tri1] at *

    all_goals linarith

  rcases hc with hc | hc

  · exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

  · exact tri1.nonneg (by norm_num [tri1, Triangle.det]) n tri1_nonnegative hc

fc_compact_decl theorem excludes : Excludes 40 box (-1) :=

  excludes_of_scaled_numerator 40 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

fc_compact_decl theorem node1 : Excludes 40 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 40 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) false (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box]) (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box])

fc_compact_decl theorem node2 : Excludes 40 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 40 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) true (by convert node0 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert node1 using 1 <;> norm_num [TBox.left, TBox.right])

namespace Leaf4

fc_compact_decl def cert : Certificate := mkCert 40 ![![0, 0, 0, 32768], ![0, 16384, 0, 0], ![16384, 0, 0, 0]] ![57344, 57344, 0]

fc_compact_decl def a : Seven := ![(-35 / 64 : ℚ), (7 / 8 : ℚ), (7 / 8 : ℚ), (7 / 8 : ℚ), (7 / 8 : ℚ), (0 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-117 : ℚ), (448 : ℚ), (-565 : ℚ)], ![(448 : ℚ), (0 : ℚ), (448 : ℚ)], ![(-565 : ℚ), (448 : ℚ), (-1013 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, 1]

fc_compact_decl def box : TBox := ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (-1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hx : x = (1 / 2 : ℝ) := by linarith

  have hy : y = (1 / 2 : ℝ) := by linarith

  rw [hx, hy]

  norm_num [numEval, n, Fin.sum_univ_three, Matrix.cons_val, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

fc_compact_decl theorem excludes : Excludes 40 box (-1) :=

  excludes_of_scaled_numerator 40 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf4

namespace Leaf5

fc_compact_decl def cert : Certificate := mkCert 40 ![![0, 0, 0, 19456], ![0, 13312, 0, 13312], ![19456, 0, 0, 0]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (-247 / 1024 : ℚ), (3211 / 16384 : ℚ), (19 / 32 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-7163 : ℚ), (35264 : ℚ), (-42427 : ℚ)], ![(-9386 : ℚ), (31616 : ℚ), (22230 : ℚ)], ![(-15067 : ℚ), (3648 : ℚ), (-18715 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, 1]

fc_compact_decl def box : TBox := ⟨(1 / 2 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (-1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    rcases h with h | h | h

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0] at *

    all_goals linarith

  exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

fc_compact_decl theorem excludes : Excludes 40 box (-1) :=

  excludes_of_scaled_numerator 40 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf5

fc_compact_decl theorem node3 : Excludes 40 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 40 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) true (by convert Leaf4.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf4.box]) (by convert Leaf5.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf5.box])

fc_compact_decl theorem node4 : Excludes 40 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 40 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert node2 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert node3 using 1 <;> norm_num [TBox.left, TBox.right])

namespace Leaf6

fc_compact_decl def cert : Certificate := mkCert 40 ![![0, 0, 0, 19456], ![0, 19456, 0, 0], ![13312, 0, 13312, 0]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (5035 / 16384 : ℚ), (57 / 512 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (247 / 512 : ℚ), (-247 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (0 : ℚ), (-15808 : ℚ)], ![(5776 : ℚ), (15808 : ℚ), (-2128 : ℚ)], ![(-12939 : ℚ), (7904 : ℚ), (-12939 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, -1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    rcases h with h | h | h

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0] at *

    all_goals linarith

  exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

fc_compact_decl theorem excludes : Excludes 40 box (1) :=

  excludes_of_scaled_numerator 40 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf6

namespace Leaf7

fc_compact_decl def cert : Certificate := mkCert 40 ![![0, 0, 0, 24576], ![0, 20480, 0, 0], ![12288, 0, 8192, 0]] ![49152, 40960, 8192]

fc_compact_decl def a : Seven := ![(73 / 480 : ℚ), (5 / 8 : ℚ), (3 / 5 : ℚ), (5 / 8 : ℚ), (3 / 8 : ℚ), (1 / 8 : ℚ), (-1 / 20 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-511 : ℚ), (2496 : ℚ), (-6271 : ℚ)], ![(4992 : ℚ), (1920 : ℚ), (4224 : ℚ)], ![(-6271 : ℚ), (3264 : ℚ), (-10111 : ℚ)]]

fc_compact_decl def scale : ℚ := 3840

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, -1]

fc_compact_decl def box : TBox := ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(1 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)⟩

fc_compact_decl theorem tri1_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri1.x u v) (tri1.y u v) :=
  triangle_nonnegative_of_coefficients n tri1 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y ∨ tri1.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    obtain ⟨h,k⟩ := h

    rcases h with h | h | h <;> rcases k with k | k | k

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0, tri1] at *

    all_goals linarith

  rcases hc with hc | hc

  · exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

  · exact tri1.nonneg (by norm_num [tri1, Triangle.det]) n tri1_nonnegative hc

fc_compact_decl theorem excludes : Excludes 40 box (1) :=

  excludes_of_scaled_numerator 40 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf7

fc_compact_decl theorem node5 : Excludes 40 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 40 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) false (by convert Leaf6.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf6.box]) (by convert Leaf7.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf7.box])

namespace Leaf8

fc_compact_decl def cert : Certificate := mkCert 40 ![![0, 0, 0, 32768], ![0, 16384, 0, 0], ![16384, 0, 0, 0]] ![57344, 57344, 0]

fc_compact_decl def a : Seven := ![(-35 / 64 : ℚ), (7 / 8 : ℚ), (7 / 8 : ℚ), (7 / 8 : ℚ), (7 / 8 : ℚ), (0 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-117 : ℚ), (448 : ℚ), (-565 : ℚ)], ![(448 : ℚ), (0 : ℚ), (448 : ℚ)], ![(-565 : ℚ), (448 : ℚ), (-1013 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, -1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hx : x = (1 / 2 : ℝ) := by linarith

  have hy : y = (1 / 2 : ℝ) := by linarith

  rw [hx, hy]

  norm_num [numEval, n, Fin.sum_univ_three, Matrix.cons_val, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

fc_compact_decl theorem excludes : Excludes 40 box (1) :=

  excludes_of_scaled_numerator 40 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf8

fc_compact_decl theorem node6 : Excludes 40 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 40 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert node5 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf8.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf8.box])

namespace Leaf9

fc_compact_decl def cert : Certificate := mkCert 40 ![![0, 0, 0, 20480], ![0, 20480, 0, 4096], ![0, 0, 20480, 0]] ![40960, 32768, 32768]

fc_compact_decl def a : Seven := ![(27 / 80 : ℚ), (29 / 240 : ℚ), (5 / 24 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (-1 / 2 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-775 : ℚ), (-3840 : ℚ), (-8455 : ℚ)], ![(5440 : ℚ), (7680 : ℚ), (-2240 : ℚ)], ![(-5543 : ℚ), (3840 : ℚ), (-5543 : ℚ)]]

fc_compact_decl def scale : ℚ := 3840

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, -1]

fc_compact_decl def box : TBox := ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 2 : ℚ), (0 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(1 / 2 : ℚ), (0 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ)⟩

fc_compact_decl theorem tri1_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri1.x u v) (tri1.y u v) :=
  triangle_nonnegative_of_coefficients n tri1 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y ∨ tri1.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    obtain ⟨h,k⟩ := h

    rcases h with h | h | h <;> rcases k with k | k | k

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0, tri1] at *

    all_goals linarith

  rcases hc with hc | hc

  · exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

  · exact tri1.nonneg (by norm_num [tri1, Triangle.det]) n tri1_nonnegative hc

fc_compact_decl theorem excludes : Excludes 40 box (1) :=

  excludes_of_scaled_numerator 40 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf9

namespace Leaf10

fc_compact_decl def cert : Certificate := mkCert 40 ![![0, 0, 0, 32768], ![0, 16384, 0, 0], ![16384, 0, 0, 0]] ![49152, 57344, 0]

fc_compact_decl def a : Seven := ![(-47 / 128 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (7 / 8 : ℚ), (0 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-103 : ℚ), (448 : ℚ), (-551 : ℚ)], ![(384 : ℚ), (0 : ℚ), (384 : ℚ)], ![(-487 : ℚ), (448 : ℚ), (-935 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, -1]

fc_compact_decl def box : TBox := ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 2 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(1 / 2 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri1_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri1.x u v) (tri1.y u v) :=
  triangle_nonnegative_of_coefficients n tri1 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y ∨ tri1.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    obtain ⟨h,k⟩ := h

    rcases h with h | h | h <;> rcases k with k | k | k

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0, tri1] at *

    all_goals linarith

  rcases hc with hc | hc

  · exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

  · exact tri1.nonneg (by norm_num [tri1, Triangle.det]) n tri1_nonnegative hc

fc_compact_decl theorem excludes : Excludes 40 box (1) :=

  excludes_of_scaled_numerator 40 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf10

fc_compact_decl theorem node7 : Excludes 40 ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 40 ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) true (by convert Leaf9.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf9.box]) (by convert Leaf10.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf10.box])

namespace Leaf11

fc_compact_decl def cert : Certificate := mkCert 40 ![![0, 0, 0, 19456], ![0, 13312, 0, 13312], ![0, 0, 19456, 0]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (-247 / 1024 : ℚ), (3211 / 16384 : ℚ), (19 / 32 : ℚ), (0 : ℚ), (247 / 512 : ℚ), (-247 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-7163 : ℚ), (-15808 : ℚ), (-42427 : ℚ)], ![(22230 : ℚ), (31616 : ℚ), (-9386 : ℚ)], ![(-15067 : ℚ), (15808 : ℚ), (-18715 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, -1]

fc_compact_decl def box : TBox := ⟨(3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(3 / 4 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ), (1 / 4 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(3 / 4 : ℚ), (0 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ)⟩

fc_compact_decl theorem tri1_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri1.x u v) (tri1.y u v) :=
  triangle_nonnegative_of_coefficients n tri1 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y ∨ tri1.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    obtain ⟨h,k⟩ := h

    rcases h with h | h | h <;> rcases k with k | k | k

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0, tri1] at *

    all_goals linarith

  rcases hc with hc | hc

  · exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

  · exact tri1.nonneg (by norm_num [tri1, Triangle.det]) n tri1_nonnegative hc

fc_compact_decl theorem excludes : Excludes 40 box (1) :=

  excludes_of_scaled_numerator 40 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf11

namespace Leaf12

fc_compact_decl def cert : Certificate := mkCert 40 ![![0, 0, 0, 24576], ![0, 16384, 0, 4096], ![20480, 0, 0, 0]] ![40960, 53248, 12288]

fc_compact_decl def a : Seven := ![(149 / 1920 : ℚ), (41 / 160 : ℚ), (7 / 16 : ℚ), (13 / 16 : ℚ), (13 / 16 : ℚ), (3 / 16 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-1253 : ℚ), (6240 : ℚ), (-8933 : ℚ)], ![(3360 : ℚ), (2880 : ℚ), (3360 : ℚ)], ![(-4661 : ℚ), (6240 : ℚ), (-9461 : ℚ)]]

fc_compact_decl def scale : ℚ := 3840

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, -1]

fc_compact_decl def box : TBox := ⟨(3 / 4 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(3 / 4 : ℚ), (1 / 4 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (1 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(3 / 4 : ℚ), (1 / 4 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri1_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri1.x u v) (tri1.y u v) :=
  triangle_nonnegative_of_coefficients n tri1 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y ∨ tri1.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    obtain ⟨h,k⟩ := h

    rcases h with h | h | h <;> rcases k with k | k | k

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0, tri1] at *

    all_goals linarith

  rcases hc with hc | hc

  · exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

  · exact tri1.nonneg (by norm_num [tri1, Triangle.det]) n tri1_nonnegative hc

fc_compact_decl theorem excludes : Excludes 40 box (1) :=

  excludes_of_scaled_numerator 40 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf12

fc_compact_decl theorem node8 : Excludes 40 ⟨(3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 40 ⟨(3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) true (by convert Leaf11.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf11.box]) (by convert Leaf12.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf12.box])

fc_compact_decl theorem node9 : Excludes 40 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 40 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) false (by convert node7 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert node8 using 1 <;> norm_num [TBox.left, TBox.right])

namespace Leaf13

fc_compact_decl def cert : Certificate := mkCert 40 ![![0, 0, 0, 19456], ![0, 13312, 0, 13312], ![19456, 0, 0, 0]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (-247 / 1024 : ℚ), (3211 / 16384 : ℚ), (19 / 32 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-7163 : ℚ), (19456 : ℚ), (-42427 : ℚ)], ![(6422 : ℚ), (31616 : ℚ), (6422 : ℚ)], ![(-15067 : ℚ), (19456 : ℚ), (-18715 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, -1]

fc_compact_decl def box : TBox := ⟨(1 / 2 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    rcases h with h | h | h

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0] at *

    all_goals linarith

  exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

fc_compact_decl theorem excludes : Excludes 40 box (1) :=

  excludes_of_scaled_numerator 40 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf13

fc_compact_decl theorem node10 : Excludes 40 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 40 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert node9 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf13.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf13.box])

fc_compact_decl theorem node11 : Excludes 40 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 40 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert node6 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert node10 using 1 <;> norm_num [TBox.left, TBox.right])

fc_compact_decl theorem node12 : Excludes 40 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 40 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node4 node11

fc_compact_decl theorem excludes : Excludes 40 TBox.unit 0 := by
  simpa [TBox.unit] using node12

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case040


/- Generated compressed exclusion certificate. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSquares.CenterElimination.Compressed.Case041

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 41 ![![0, 0, 0, 32768], ![24576, 0, 0, 0], ![0, 8192, 0, 0]] ![73728, 81920, 90112]

fc_compact_decl def a : Seven := ![(-2563 / 384 : ℚ), (8 : ℚ), (33 / 16 : ℚ), (0 : ℚ), (5 / 4 : ℚ), (11 / 8 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(799 : ℚ), (1920 : ℚ), (-1313 : ℚ)], ![(3168 : ℚ), (4224 : ℚ), (3168 : ℚ)], ![(-13601 : ℚ), (1920 : ℚ), (-11489 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, 1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(0 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(0 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri1_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri1.x u v) (tri1.y u v) :=
  triangle_nonnegative_of_coefficients n tri1 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (-1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y ∨ tri1.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    obtain ⟨h,k⟩ := h

    rcases h with h | h | h <;> rcases k with k | k | k

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0, tri1] at *

    all_goals linarith

  rcases hc with hc | hc

  · exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

  · exact tri1.nonneg (by norm_num [tri1, Triangle.det]) n tri1_nonnegative hc

fc_compact_decl theorem excludes : Excludes 41 box (-1) :=

  excludes_of_scaled_numerator 41 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 41 ![![0, 0, 0, 32768], ![8192, 0, 0, 0], ![0, 24576, 0, 0]] ![81920, 73728, 90112]

fc_compact_decl def a : Seven := ![(-2563 / 384 : ℚ), (53 / 16 : ℚ), (55 / 8 : ℚ), (0 : ℚ), (9 / 8 : ℚ), (11 / 8 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-2801 : ℚ), (1728 : ℚ), (-4913 : ℚ)], ![(10560 : ℚ), (4224 : ℚ), (10560 : ℚ)], ![(-10001 : ℚ), (1728 : ℚ), (-7889 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, 1]

fc_compact_decl def box : TBox := ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (-1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    rcases h with h | h | h

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0] at *

    all_goals linarith

  exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

fc_compact_decl theorem excludes : Excludes 41 box (-1) :=

  excludes_of_scaled_numerator 41 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 41 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 41 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box])

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 41 ![![0, 0, 0, 32768], ![24576, 0, 0, 0], ![0, 8192, 0, 0]] ![73728, 81920, 90112]

fc_compact_decl def a : Seven := ![(-2563 / 384 : ℚ), (8 : ℚ), (33 / 16 : ℚ), (0 : ℚ), (5 / 4 : ℚ), (11 / 8 : ℚ), (-11 / 8 : ℚ)]

fc_compact_decl def n : Numerator := ![![(799 : ℚ), (-192 : ℚ), (-1313 : ℚ)], ![(5280 : ℚ), (4224 : ℚ), (1056 : ℚ)], ![(-13601 : ℚ), (4032 : ℚ), (-11489 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, -1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(0 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    rcases h with h | h | h

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0] at *

    all_goals linarith

  exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

fc_compact_decl theorem excludes : Excludes 41 box (1) :=

  excludes_of_scaled_numerator 41 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 41 ![![0, 0, 0, 32768], ![8192, 0, 0, 0], ![0, 24576, 0, 0]] ![40960, 32768, 49152]

fc_compact_decl def a : Seven := ![(-343 / 384 : ℚ), (9 / 8 : ℚ), (15 / 8 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (-3 / 4 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-521 : ℚ), (-384 : ℚ), (-1673 : ℚ)], ![(4032 : ℚ), (2304 : ℚ), (1728 : ℚ)], ![(-3401 : ℚ), (1920 : ℚ), (-2249 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, -1]

fc_compact_decl def box : TBox := ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 2 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(1 / 2 : ℚ), (0 : ℚ), (1 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri1_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri1.x u v) (tri1.y u v) :=
  triangle_nonnegative_of_coefficients n tri1 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y ∨ tri1.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    obtain ⟨h,k⟩ := h

    rcases h with h | h | h <;> rcases k with k | k | k

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0, tri1] at *

    all_goals linarith

  rcases hc with hc | hc

  · exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

  · exact tri1.nonneg (by norm_num [tri1, Triangle.det]) n tri1_nonnegative hc

fc_compact_decl theorem excludes : Excludes 41 box (1) :=

  excludes_of_scaled_numerator 41 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

fc_compact_decl theorem node1 : Excludes 41 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 41 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box]) (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box])

fc_compact_decl theorem node2 : Excludes 41 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 41 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node0 node1

fc_compact_decl theorem excludes : Excludes 41 TBox.unit 0 := by
  simpa [TBox.unit] using node2

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case041


/- Generated compressed exclusion certificate. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSquares.CenterElimination.Compressed.Case042

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 42 ![![0, 0, 24576, 0], ![0, 32768, 0, 0], ![0, 0, 8192, 0]] ![49152, 57344, 57344]

fc_compact_decl def a : Seven := ![(-811 / 384 : ℚ), (61 / 16 : ℚ), (3 / 32 : ℚ), (0 : ℚ), (7 / 8 : ℚ), (7 / 8 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(703 : ℚ), (1344 : ℚ), (-641 : ℚ)], ![(144 : ℚ), (2688 : ℚ), (144 : ℚ)], ![(-6497 : ℚ), (1344 : ℚ), (-5153 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, 1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(0 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(0 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri1_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri1.x u v) (tri1.y u v) :=
  triangle_nonnegative_of_coefficients n tri1 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (-1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y ∨ tri1.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    obtain ⟨h,k⟩ := h

    rcases h with h | h | h <;> rcases k with k | k | k

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0, tri1] at *

    all_goals linarith

  rcases hc with hc | hc

  · exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

  · exact tri1.nonneg (by norm_num [tri1, Triangle.det]) n tri1_nonnegative hc

fc_compact_decl theorem excludes : Excludes 42 box (-1) :=

  excludes_of_scaled_numerator 42 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 42 ![![0, 0, 19456, 0], ![0, 13312, 0, 13312], ![0, 0, 19456, 0]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (741 / 1024 : ℚ), (3211 / 16384 : ℚ), (0 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-1083 : ℚ), (19456 : ℚ), (-16891 : ℚ)], ![(6422 : ℚ), (31616 : ℚ), (6422 : ℚ)], ![(-40603 : ℚ), (19456 : ℚ), (-24795 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, 1]

fc_compact_decl def box : TBox := ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (-1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    rcases h with h | h | h

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0] at *

    all_goals linarith

  exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

fc_compact_decl theorem excludes : Excludes 42 box (-1) :=

  excludes_of_scaled_numerator 42 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 42 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 42 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box])

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 42 ![![0, 0, 24576, 0], ![0, 28672, 0, 0], ![0, 0, 12288, 0]] ![49152, 53248, 53248]

fc_compact_decl def a : Seven := ![(-2417 / 2688 : ℚ), (241 / 96 : ℚ), (3 / 56 : ℚ), (0 : ℚ), (13 / 16 : ℚ), (13 / 16 : ℚ), (-13 / 16 : ℚ)]

fc_compact_decl def n : Numerator := ![![(4105 : ℚ), (0 : ℚ), (-4631 : ℚ)], ![(9312 : ℚ), (17472 : ℚ), (-8160 : ℚ)], ![(-31623 : ℚ), (17472 : ℚ), (-22887 : ℚ)]]

fc_compact_decl def scale : ℚ := 5376

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, -1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(0 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    rcases h with h | h | h

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0] at *

    all_goals linarith

  exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

fc_compact_decl theorem excludes : Excludes 42 box (1) :=

  excludes_of_scaled_numerator 42 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 42 ![![0, 0, 19456, 0], ![0, 13312, 0, 13312], ![0, 0, 0, 19456]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (741 / 1024 : ℚ), (3211 / 16384 : ℚ), (19 / 32 : ℚ), (19 / 32 : ℚ), (0 : ℚ), (-247 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(741 : ℚ), (3648 : ℚ), (-18715 : ℚ)], ![(22230 : ℚ), (0 : ℚ), (-9386 : ℚ)], ![(-22971 : ℚ), (35264 : ℚ), (-42427 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, -1]

fc_compact_decl def box : TBox := ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 2 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(1 / 2 : ℚ), (0 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri1_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri1.x u v) (tri1.y u v) :=
  triangle_nonnegative_of_coefficients n tri1 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y ∨ tri1.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    obtain ⟨h,k⟩ := h

    rcases h with h | h | h <;> rcases k with k | k | k

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0, tri1] at *

    all_goals linarith

  rcases hc with hc | hc

  · exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

  · exact tri1.nonneg (by norm_num [tri1, Triangle.det]) n tri1_nonnegative hc

fc_compact_decl theorem excludes : Excludes 42 box (1) :=

  excludes_of_scaled_numerator 42 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

namespace Leaf4

fc_compact_decl def cert : Certificate := mkCert 42 ![![0, 0, 19456, 0], ![0, 13312, 0, 13312], ![0, 0, 19456, 0]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (741 / 1024 : ℚ), (3211 / 16384 : ℚ), (0 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (-247 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-1083 : ℚ), (3648 : ℚ), (-16891 : ℚ)], ![(22230 : ℚ), (31616 : ℚ), (-9386 : ℚ)], ![(-40603 : ℚ), (35264 : ℚ), (-24795 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, -1]

fc_compact_decl def box : TBox := ⟨(1 / 2 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    rcases h with h | h | h

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0] at *

    all_goals linarith

  exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

fc_compact_decl theorem excludes : Excludes 42 box (1) :=

  excludes_of_scaled_numerator 42 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf4

fc_compact_decl theorem node1 : Excludes 42 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 42 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box]) (by convert Leaf4.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf4.box])

fc_compact_decl theorem node2 : Excludes 42 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 42 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box]) (by convert node1 using 1 <;> norm_num [TBox.left, TBox.right])

fc_compact_decl theorem node3 : Excludes 42 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 42 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node0 node2

fc_compact_decl theorem excludes : Excludes 42 TBox.unit 0 := by
  simpa [TBox.unit] using node3

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case042


/- Generated compressed exclusion certificate. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSquares.CenterElimination.Compressed.Case043

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 43 ![![0, 0, 19456, 0], ![19456, 0, 0, 0], ![0, 13312, 0, 13312]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (5035 / 16384 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (7904 : ℚ), (-15808 : ℚ)], ![(3952 : ℚ), (15808 : ℚ), (11856 : ℚ)], ![(-12939 : ℚ), (0 : ℚ), (-12939 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, 1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(0 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (-1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    rcases h with h | h | h

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0] at *

    all_goals linarith

  exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

fc_compact_decl theorem excludes : Excludes 43 box (-1) :=

  excludes_of_scaled_numerator 43 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 43 ![![0, 0, 16384, 0], ![16384, 0, 0, 0], ![0, 0, 0, 32768]] ![40960, 32768, 40960]

fc_compact_decl def a : Seven := ![(1 / 128 : ℚ), (5 / 16 : ℚ), (25 / 32 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ), (5 / 8 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-55 : ℚ), (576 : ℚ), (-631 : ℚ)], ![(80 : ℚ), (640 : ℚ), (720 : ℚ)], ![(-535 : ℚ), (-64 : ℚ), (-471 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, 1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (3 / 4 : ℚ)⟩

fc_compact_decl theorem tri1_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri1.x u v) (tri1.y u v) :=
  triangle_nonnegative_of_coefficients n tri1 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (-1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y ∨ tri1.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    obtain ⟨h,k⟩ := h

    rcases h with h | h | h <;> rcases k with k | k | k

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0, tri1] at *

    all_goals linarith

  rcases hc with hc | hc

  · exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

  · exact tri1.nonneg (by norm_num [tri1, Triangle.det]) n tri1_nonnegative hc

fc_compact_decl theorem excludes : Excludes 43 box (-1) :=

  excludes_of_scaled_numerator 43 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 43 ![![0, 0, 19456, 0], ![19456, 0, 0, 0], ![0, 0, 13312, 13312]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (5035 / 16384 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (247 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-3952 : ℚ), (15808 : ℚ), (-11856 : ℚ)], ![(0 : ℚ), (7904 : ℚ), (15808 : ℚ)], ![(-12939 : ℚ), (0 : ℚ), (-12939 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, 1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(0 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(0 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri1_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri1.x u v) (tri1.y u v) :=
  triangle_nonnegative_of_coefficients n tri1 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (-1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y ∨ tri1.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    obtain ⟨h,k⟩ := h

    rcases h with h | h | h <;> rcases k with k | k | k

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0, tri1] at *

    all_goals linarith

  rcases hc with hc | hc

  · exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

  · exact tri1.nonneg (by norm_num [tri1, Triangle.det]) n tri1_nonnegative hc

fc_compact_decl theorem excludes : Excludes 43 box (-1) :=

  excludes_of_scaled_numerator 43 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

fc_compact_decl theorem node0 : Excludes 43 ⟨(0 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 43 ⟨(0 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) true (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box]) (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box])

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 43 ![![0, 0, 16384, 0], ![16384, 0, 0, 0], ![0, 0, 0, 32768]] ![49152, 32768, 57344]

fc_compact_decl def a : Seven := ![(-67 / 128 : ℚ), (5 / 16 : ℚ), (21 / 16 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (7 / 8 : ℚ), (7 / 8 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-127 : ℚ), (704 : ℚ), (-831 : ℚ)], ![(224 : ℚ), (896 : ℚ), (1120 : ℚ)], ![(-735 : ℚ), (-192 : ℚ), (-543 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, 1]

fc_compact_decl def box : TBox := ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (1 / 4 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri1_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri1.x u v) (tri1.y u v) :=
  triangle_nonnegative_of_coefficients n tri1 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (-1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y ∨ tri1.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    obtain ⟨h,k⟩ := h

    rcases h with h | h | h <;> rcases k with k | k | k

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0, tri1] at *

    all_goals linarith

  rcases hc with hc | hc

  · exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

  · exact tri1.nonneg (by norm_num [tri1, Triangle.det]) n tri1_nonnegative hc

fc_compact_decl theorem excludes : Excludes 43 box (-1) :=

  excludes_of_scaled_numerator 43 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

fc_compact_decl theorem node1 : Excludes 43 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 43 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) false (by convert node0 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box])

fc_compact_decl theorem node2 : Excludes 43 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 43 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) true (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert node1 using 1 <;> norm_num [TBox.left, TBox.right])

namespace Leaf4

fc_compact_decl def cert : Certificate := mkCert 43 ![![0, 0, 24576, 0], ![16384, 0, 0, 0], ![0, 0, 0, 24576]] ![49152, 49152, 49152]

fc_compact_decl def a : Seven := ![(-3 / 8 : ℚ), (0 : ℚ), (9 / 8 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-137 : ℚ), (768 : ℚ), (-905 : ℚ)], ![(192 : ℚ), (768 : ℚ), (960 : ℚ)], ![(-521 : ℚ), (0 : ℚ), (-521 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, 1]

fc_compact_decl def box : TBox := ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (-1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    rcases h with h | h | h

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0] at *

    all_goals linarith

  exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

fc_compact_decl theorem excludes : Excludes 43 box (-1) :=

  excludes_of_scaled_numerator 43 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf4

fc_compact_decl theorem node3 : Excludes 43 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 43 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert node2 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf4.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf4.box])

namespace Leaf5

fc_compact_decl def cert : Certificate := mkCert 43 ![![0, 0, 19456, 0], ![19456, 0, 0, 0], ![0, 13312, 0, 13312]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (5035 / 16384 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (247 / 512 : ℚ), (-247 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (0 : ℚ), (-15808 : ℚ)], ![(11856 : ℚ), (15808 : ℚ), (3952 : ℚ)], ![(-12939 : ℚ), (7904 : ℚ), (-12939 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, -1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(0 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    rcases h with h | h | h

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0] at *

    all_goals linarith

  exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

fc_compact_decl theorem excludes : Excludes 43 box (1) :=

  excludes_of_scaled_numerator 43 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf5

namespace Leaf6

fc_compact_decl def cert : Certificate := mkCert 43 ![![0, 0, 24576, 0], ![10240, 0, 0, 0], ![0, 30720, 0, 0]] ![73728, 34816, 81920]

fc_compact_decl def a : Seven := ![(-27913 / 7680 : ℚ), (5 / 12 : ℚ), (9 / 2 : ℚ), (17 / 32 : ℚ), (0 : ℚ), (5 / 4 : ℚ), (-5 / 4 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-23783 : ℚ), (-19200 : ℚ), (-51143 : ℚ)], ![(88320 : ℚ), (38400 : ℚ), (49920 : ℚ)], ![(-49383 : ℚ), (19200 : ℚ), (-38343 : ℚ)]]

fc_compact_decl def scale : ℚ := 7680

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, 1, -1]

fc_compact_decl def box : TBox := ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 2 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(1 / 2 : ℚ), (0 : ℚ), (1 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri1_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri1.x u v) (tri1.y u v) :=
  triangle_nonnegative_of_coefficients n tri1 (by decide +kernel) u v hu hv hs

fc_compact_decl theorem nonnegative (x y : ℝ) (hb : box.Contains x y)
    (hr : RegionHolds (1) x y) : 0 ≤ numEval n x y := by
  obtain ⟨h1,h2,h3,h4⟩ := hb
  norm_num [box] at h1 h2 h3 h4
  norm_num [RegionHolds] at hr

  have hc : tri0.Contains x y ∨ tri1.Contains x y := by

    by_contra h

    simp only [not_or, Triangle.Contains, not_and_or, not_le] at h

    obtain ⟨h,k⟩ := h

    rcases h with h | h | h <;> rcases k with k | k | k

    all_goals norm_num [Triangle.u, Triangle.v, Triangle.det, tri0, tri1] at *

    all_goals linarith

  rcases hc with hc | hc

  · exact tri0.nonneg (by norm_num [tri0, Triangle.det]) n tri0_nonnegative hc

  · exact tri1.nonneg (by norm_num [tri1, Triangle.det]) n tri1_nonnegative hc

fc_compact_decl theorem excludes : Excludes 43 box (1) :=

  excludes_of_scaled_numerator 43 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf6

fc_compact_decl theorem node4 : Excludes 43 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 43 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert Leaf5.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf5.box]) (by convert Leaf6.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf6.box])

fc_compact_decl theorem node5 : Excludes 43 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 43 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node3 node4

fc_compact_decl theorem excludes : Excludes 43 TBox.unit 0 := by
  simpa [TBox.unit] using node5

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case043
