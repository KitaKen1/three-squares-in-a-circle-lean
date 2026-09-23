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

namespace ThreeSquares.CenterElimination.Compressed.Case104

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 104 ![![0, 0, 0, 19456], ![0, 19456, 0, 0], ![13312, 0, 13312, 0]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (19 / 32 : ℚ), (57 / 512 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (3211 / 16384 : ℚ), (247 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (11856 : ℚ), (-11115 : ℚ)], ![(-2128 : ℚ), (6422 : ℚ), (5776 : ℚ)], ![(-12939 : ℚ), (3952 : ℚ), (-17632 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 104 box (-1) :=

  excludes_of_scaled_numerator 104 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 104 ![![0, 0, 0, 8192], ![0, 24576, 0, 0], ![32768, 0, 0, 0]] ![40960, 32768, 24576]

fc_compact_decl def a : Seven := ![(-127 / 384 : ℚ), (5 / 8 : ℚ), (5 / 16 : ℚ), (1 / 2 : ℚ), (5 / 4 : ℚ), (3 / 16 : ℚ), (3 / 8 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-521 : ℚ), (2496 : ℚ), (-1577 : ℚ)], ![(-96 : ℚ), (576 : ℚ), (1056 : ℚ)], ![(-1769 : ℚ), (1344 : ℚ), (-2249 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, 1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩

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

fc_compact_decl theorem excludes : Excludes 104 box (-1) :=

  excludes_of_scaled_numerator 104 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 104 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 104 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) true (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box])

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 104 ![![0, 0, 0, 12288], ![0, 28672, 0, 0], ![12288, 0, 12288, 0]] ![86016, 77824, 0]

fc_compact_decl def a : Seven := ![(-449 / 128 : ℚ), (21 / 16 : ℚ), (21 / 16 : ℚ), (19 / 16 : ℚ), (133 / 32 : ℚ), (0 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-683 : ℚ), (2128 : ℚ), (-1291 : ℚ)], ![(672 : ℚ), (0 : ℚ), (672 : ℚ)], ![(-1355 : ℚ), (2128 : ℚ), (-1963 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 104 box (-1) :=

  excludes_of_scaled_numerator 104 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

fc_compact_decl theorem node1 : Excludes 104 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 104 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert node0 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box])

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 104 ![![0, 0, 0, 19456], ![0, 19456, 0, 0], ![13312, 0, 13312, 0]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (19 / 32 : ℚ), (57 / 512 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (3211 / 16384 : ℚ), (-247 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (3952 : ℚ), (-11115 : ℚ)], ![(5776 : ℚ), (6422 : ℚ), (-2128 : ℚ)], ![(-12939 : ℚ), (11856 : ℚ), (-17632 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 104 box (1) :=

  excludes_of_scaled_numerator 104 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

namespace Leaf4

fc_compact_decl def cert : Certificate := mkCert 104 ![![0, 0, 0, 24576], ![0, 24576, 0, 0], ![4096, 0, 12288, 0]] ![53248, 40960, 12288]

fc_compact_decl def a : Seven := ![(21 / 256 : ℚ), (13 / 16 : ℚ), (39 / 64 : ℚ), (5 / 8 : ℚ), (65 / 96 : ℚ), (-3 / 64 : ℚ), (-9 / 64 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-18 : ℚ), (103 : ℚ), (-129 : ℚ)], ![(144 : ℚ), (-18 : ℚ), (90 : ℚ)], ![(-165 : ℚ), (157 : ℚ), (-294 : ℚ)]]

fc_compact_decl def scale : ℚ := 96

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 104 box (1) :=

  excludes_of_scaled_numerator 104 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf4

fc_compact_decl theorem node2 : Excludes 104 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 104 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) false (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box]) (by convert Leaf4.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf4.box])

namespace Leaf5

fc_compact_decl def cert : Certificate := mkCert 104 ![![0, 0, 0, 16384], ![0, 32768, 0, 0], ![8192, 0, 8192, 0]] ![81920, 65536, 0]

fc_compact_decl def a : Seven := ![(-65 / 32 : ℚ), (5 / 4 : ℚ), (5 / 4 : ℚ), (1 : ℚ), (5 / 2 : ℚ), (0 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-369 : ℚ), (1280 : ℚ), (-881 : ℚ)], ![(640 : ℚ), (0 : ℚ), (640 : ℚ)], ![(-1009 : ℚ), (1280 : ℚ), (-1521 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 104 box (1) :=

  excludes_of_scaled_numerator 104 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf5

fc_compact_decl theorem node3 : Excludes 104 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 104 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert node2 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf5.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf5.box])

namespace Leaf6

fc_compact_decl def cert : Certificate := mkCert 104 ![![0, 0, 0, 20480], ![0, 20480, 0, 4096], ![0, 0, 20480, 0]] ![45056, 36864, 24576]

fc_compact_decl def a : Seven := ![(521 / 1920 : ℚ), (55 / 96 : ℚ), (11 / 32 : ℚ), (9 / 16 : ℚ), (99 / 160 : ℚ), (3 / 80 : ℚ), (-3 / 8 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-829 : ℚ), (1872 : ℚ), (-5437 : ℚ)], ![(5520 : ℚ), (576 : ℚ), (-240 : ℚ)], ![(-5517 : ℚ), (7632 : ℚ), (-9549 : ℚ)]]

fc_compact_decl def scale : ℚ := 3840

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

fc_compact_decl def box : TBox := ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 2 : ℚ), (0 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(1 / 2 : ℚ), (0 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)⟩

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

fc_compact_decl theorem excludes : Excludes 104 box (1) :=

  excludes_of_scaled_numerator 104 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf6

namespace Leaf7

fc_compact_decl def cert : Certificate := mkCert 104 ![![0, 0, 0, 19456], ![0, 13312, 0, 13312], ![0, 0, 19456, 0]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (247 / 1024 : ℚ), (3211 / 16384 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (0 : ℚ), (-247 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-7163 : ℚ), (0 : ℚ), (-26619 : ℚ)], ![(22230 : ℚ), (0 : ℚ), (-9386 : ℚ)], ![(-15067 : ℚ), (31616 : ℚ), (-34523 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 104 box (1) :=

  excludes_of_scaled_numerator 104 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf7

namespace Leaf8

fc_compact_decl def cert : Certificate := mkCert 104 ![![0, 0, 0, 16384], ![0, 16384, 0, 8192], ![12288, 0, 12288, 0]] ![57344, 53248, 0]

fc_compact_decl def a : Seven := ![(-131 / 256 : ℚ), (7 / 12 : ℚ), (7 / 8 : ℚ), (13 / 16 : ℚ), (91 / 64 : ℚ), (0 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-149 : ℚ), (546 : ℚ), (-461 : ℚ)], ![(336 : ℚ), (0 : ℚ), (336 : ℚ)], ![(-373 : ℚ), (546 : ℚ), (-685 : ℚ)]]

fc_compact_decl def scale : ℚ := 192

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 104 box (1) :=

  excludes_of_scaled_numerator 104 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf8

fc_compact_decl theorem node4 : Excludes 104 ⟨(3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 104 ⟨(3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) true (by convert Leaf7.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf7.box]) (by convert Leaf8.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf8.box])

fc_compact_decl theorem node5 : Excludes 104 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 104 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) false (by convert Leaf6.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf6.box]) (by convert node4 using 1 <;> norm_num [TBox.left, TBox.right])

namespace Leaf9

fc_compact_decl def cert : Certificate := mkCert 104 ![![0, 0, 0, 16384], ![0, 20480, 0, 4096], ![12288, 0, 12288, 0]] ![77824, 65536, 0]

fc_compact_decl def a : Seven := ![(-431 / 256 : ℚ), (95 / 96 : ℚ), (19 / 16 : ℚ), (1 : ℚ), (19 / 8 : ℚ), (0 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-65 : ℚ), (228 : ℚ), (-161 : ℚ)], ![(114 : ℚ), (0 : ℚ), (114 : ℚ)], ![(-160 : ℚ), (228 : ℚ), (-256 : ℚ)]]

fc_compact_decl def scale : ℚ := 48

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 104 box (1) :=

  excludes_of_scaled_numerator 104 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf9

fc_compact_decl theorem node6 : Excludes 104 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 104 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert node5 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf9.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf9.box])

fc_compact_decl theorem node7 : Excludes 104 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 104 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert node3 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert node6 using 1 <;> norm_num [TBox.left, TBox.right])

fc_compact_decl theorem node8 : Excludes 104 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 104 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node1 node7

fc_compact_decl theorem excludes : Excludes 104 TBox.unit 0 := by
  simpa [TBox.unit] using node8

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case104


/- Generated compressed exclusion certificate. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSquares.CenterElimination.Compressed.Case105

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 105 ![![0, 0, 0, 16384], ![32768, 0, 0, 0], ![0, 0, 16384, 0]] ![40960, 40960, 40960]

fc_compact_decl def a : Seven := ![(-5 / 64 : ℚ), (5 / 8 : ℚ), (25 / 64 : ℚ), (5 / 8 : ℚ), (25 / 32 : ℚ), (25 / 32 : ℚ), (5 / 8 : ℚ)]

fc_compact_decl def n : Numerator := ![![(75 : ℚ), (720 : ℚ), (-645 : ℚ)], ![(-120 : ℚ), (800 : ℚ), (520 : ℚ)], ![(-645 : ℚ), (80 : ℚ), (-565 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, 1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(0 : ℚ), (0 : ℚ), (1 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩

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

fc_compact_decl theorem excludes : Excludes 105 box (-1) :=

  excludes_of_scaled_numerator 105 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 105 ![![0, 0, 0, 24576], ![24576, 0, 0, 0], ![16384, 0, 0, 0]] ![49152, 57344, 57344]

fc_compact_decl def a : Seven := ![(-77 / 96 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (7 / 8 : ℚ), (7 / 8 : ℚ), (49 / 32 : ℚ), (-7 / 8 : ℚ)]

fc_compact_decl def n : Numerator := ![![(533 : ℚ), (0 : ℚ), (-3163 : ℚ)], ![(2688 : ℚ), (4704 : ℚ), (0 : ℚ)], ![(-2971 : ℚ), (2688 : ℚ), (-1963 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(0 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ), (1 : ℚ)⟩

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

fc_compact_decl theorem excludes : Excludes 105 box (1) :=

  excludes_of_scaled_numerator 105 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 105 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 105 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) Leaf0.excludes Leaf1.excludes

fc_compact_decl theorem excludes : Excludes 105 TBox.unit 0 := by
  simpa [TBox.unit] using node0

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case105


/- Generated compressed exclusion certificate. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSquares.CenterElimination.Compressed.Case106

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 106 ![![0, 0, 28672, 0], ![0, 24576, 0, 0], ![0, 12288, 0, 0]] ![12288, 40960, 32768]

fc_compact_decl def a : Seven := ![(67 / 2688 : ℚ), (3 / 16 : ℚ), (1 / 16 : ℚ), (5 / 8 : ℚ), (55 / 112 : ℚ), (5 / 6 : ℚ), (1 / 2 : ℚ)]

fc_compact_decl def n : Numerator := ![![(57 : ℚ), (10656 : ℚ), (-15623 : ℚ)], ![(-4704 : ℚ), (17920 : ℚ), (6048 : ℚ)], ![(-10919 : ℚ), (-96 : ℚ), (-8679 : ℚ)]]

fc_compact_decl def scale : ℚ := 5376

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 106 box (-1) :=

  excludes_of_scaled_numerator 106 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 106 ![![0, 0, 13312, 13312], ![0, 19456, 0, 0], ![0, 19456, 0, 0]] ![31616, 31616, 38912]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (247 / 512 : ℚ), (0 : ℚ), (247 / 1024 : ℚ), (3211 / 16384 : ℚ), (247 / 512 : ℚ), (19 / 32 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-1083 : ℚ), (25878 : ℚ), (-24795 : ℚ)], ![(-19456 : ℚ), (31616 : ℚ), (19456 : ℚ)], ![(-32699 : ℚ), (-13034 : ℚ), (-24795 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 106 box (-1) :=

  excludes_of_scaled_numerator 106 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 106 ![![0, 0, 16384, 8192], ![0, 12288, 0, 12288], ![0, 16384, 0, 0]] ![0, 65536, 61440]

fc_compact_decl def a : Seven := ![(-781 / 768 : ℚ), (0 : ℚ), (0 : ℚ), (2 / 3 : ℚ), (1 : ℚ), (15 / 8 : ℚ), (15 / 16 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-13 : ℚ), (372 : ℚ), (-501 : ℚ)], ![(-180 : ℚ), (720 : ℚ), (180 : ℚ)], ![(-373 : ℚ), (12 : ℚ), (-141 : ℚ)]]

fc_compact_decl def scale : ℚ := 96

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 106 box (-1) :=

  excludes_of_scaled_numerator 106 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

fc_compact_decl theorem node0 : Excludes 106 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 106 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) false (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box]) (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box])

fc_compact_decl theorem node1 : Excludes 106 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 106 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) true (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert node0 using 1 <;> norm_num [TBox.left, TBox.right])

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 106 ![![0, 0, 20480, 9216], ![0, 13312, 0, 13312], ![0, 9216, 0, 0]] ![0, 86016, 79872]

fc_compact_decl def a : Seven := ![(-8979 / 1856 : ℚ), (0 : ℚ), (0 : ℚ), (105 / 116 : ℚ), (21 / 16 : ℚ), (91 / 16 : ℚ), (39 / 32 : ℚ)]

fc_compact_decl def n : Numerator := ![![(703 : ℚ), (37584 : ℚ), (-97185 : ℚ)], ![(-18096 : ℚ), (168896 : ℚ), (18096 : ℚ)], ![(-83745 : ℚ), (1392 : ℚ), (-12737 : ℚ)]]

fc_compact_decl def scale : ℚ := 7424

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 106 box (-1) :=

  excludes_of_scaled_numerator 106 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

fc_compact_decl theorem node2 : Excludes 106 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 106 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert node1 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box])

namespace Leaf4

fc_compact_decl def cert : Certificate := mkCert 106 ![![0, 0, 26624, 0], ![0, 28672, 0, 0], ![0, 0, 0, 10240]] ![38912, 69632, 59392]

fc_compact_decl def a : Seven := ![(-124647 / 58240 : ℚ), (19 / 32 : ℚ), (-19 / 896 : ℚ), (17 / 16 : ℚ), (119 / 416 : ℚ), (493 / 160 : ℚ), (-29 / 32 : ℚ)]

fc_compact_decl def n : Numerator := ![![(109155 : ℚ), (-144480 : ℚ), (-856173 : ℚ)], ![(206180 : ℚ), (1435616 : ℚ), (-216060 : ℚ)], ![(-746973 : ℚ), (277760 : ℚ), (-276685 : ℚ)]]

fc_compact_decl def scale : ℚ := 116480

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 106 box (1) :=

  excludes_of_scaled_numerator 106 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf4

namespace Leaf5

fc_compact_decl def cert : Certificate := mkCert 106 ![![0, 0, 19456, 0], ![0, 19456, 0, 13312], ![0, 0, 0, 13312]] ![31616, 38912, 38912]

fc_compact_decl def a : Seven := ![(935427 / 6815744 : ℚ), (4693 / 16384 : ℚ), (3211 / 16384 : ℚ), (19 / 32 : ℚ), (57 / 512 : ℚ), (361 / 416 : ℚ), (-19 / 32 : ℚ)]

fc_compact_decl def n : Numerator := ![![(1533987 : ℚ), (-6576128 : ℚ), (-18388957 : ℚ)], ![(10765248 : ℚ), (23658496 : ℚ), (-5422144 : ℚ)], ![(-14199837 : ℚ), (9611264 : ℚ), (-10464285 : ℚ)]]

fc_compact_decl def scale : ℚ := 6815744

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

fc_compact_decl def box : TBox := ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 2 : ℚ), (0 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(1 / 2 : ℚ), (0 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)⟩

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

fc_compact_decl theorem excludes : Excludes 106 box (1) :=

  excludes_of_scaled_numerator 106 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf5

namespace Leaf6

fc_compact_decl def cert : Certificate := mkCert 106 ![![0, 0, 19456, 0], ![0, 13312, 0, 13312], ![0, 0, 0, 19456]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (247 / 1024 : ℚ), (3211 / 16384 : ℚ), (19 / 32 : ℚ), (57 / 512 : ℚ), (247 / 512 : ℚ), (-247 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(741 : ℚ), (-12160 : ℚ), (-34523 : ℚ)], ![(22230 : ℚ), (31616 : ℚ), (-9386 : ℚ)], ![(-22971 : ℚ), (19456 : ℚ), (-26619 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

fc_compact_decl def box : TBox := ⟨(3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(3 / 4 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(3 / 4 : ℚ), (0 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ)⟩

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

fc_compact_decl theorem excludes : Excludes 106 box (1) :=

  excludes_of_scaled_numerator 106 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf6

fc_compact_decl theorem node3 : Excludes 106 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 106 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) false (by convert Leaf5.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf5.box]) (by convert Leaf6.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf6.box])

namespace Leaf7

fc_compact_decl def cert : Certificate := mkCert 106 ![![0, 0, 28672, 0], ![0, 16384, 0, 16384], ![0, 0, 0, 4096]] ![0, 53248, 49152]

fc_compact_decl def a : Seven := ![(-865 / 224 : ℚ), (0 : ℚ), (0 : ℚ), (13 / 16 : ℚ), (13 / 16 : ℚ), (39 / 8 : ℚ), (-3 / 4 : ℚ)]

fc_compact_decl def n : Numerator := ![![(297 : ℚ), (224 : ℚ), (-20087 : ℚ)], ![(2688 : ℚ), (34944 : ℚ), (-2688 : ℚ)], ![(-17175 : ℚ), (5600 : ℚ), (-2615 : ℚ)]]

fc_compact_decl def scale : ℚ := 1792

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

fc_compact_decl def box : TBox := ⟨(1 / 2 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ)⟩

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

fc_compact_decl theorem excludes : Excludes 106 box (1) :=

  excludes_of_scaled_numerator 106 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf7

namespace Leaf8

fc_compact_decl def cert : Certificate := mkCert 106 ![![0, 0, 24576, 0], ![0, 16384, 0, 16384], ![0, 0, 0, 8192]] ![0, 49152, 40960]

fc_compact_decl def a : Seven := ![(-125 / 128 : ℚ), (0 : ℚ), (0 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (15 / 8 : ℚ), (-5 / 8 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-3 : ℚ), (64 : ℚ), (-1347 : ℚ)], ![(320 : ℚ), (1920 : ℚ), (-320 : ℚ)], ![(-963 : ℚ), (704 : ℚ), (-387 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

fc_compact_decl def box : TBox := ⟨(3 / 4 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(3 / 4 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (3 / 4 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(3 / 4 : ℚ), (1 / 2 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ)⟩

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

fc_compact_decl theorem excludes : Excludes 106 box (1) :=

  excludes_of_scaled_numerator 106 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf8

namespace Leaf9

fc_compact_decl def cert : Certificate := mkCert 106 ![![0, 0, 20480, 8192], ![0, 16384, 0, 16384], ![0, 0, 0, 4096]] ![0, 49152, 49152]

fc_compact_decl def a : Seven := ![(-759 / 224 : ℚ), (0 : ℚ), (0 : ℚ), (15 / 28 : ℚ), (3 / 4 : ℚ), (9 / 2 : ℚ), (-3 / 4 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-23 : ℚ), (0 : ℚ), (-18071 : ℚ)], ![(2688 : ℚ), (32256 : ℚ), (-2688 : ℚ)], ![(-16151 : ℚ), (5376 : ℚ), (-1943 : ℚ)]]

fc_compact_decl def scale : ℚ := 1792

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

fc_compact_decl def box : TBox := ⟨(3 / 4 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (1 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(3 / 4 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (1 : ℚ), (1 : ℚ)⟩

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

fc_compact_decl theorem excludes : Excludes 106 box (1) :=

  excludes_of_scaled_numerator 106 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf9

fc_compact_decl theorem node4 : Excludes 106 ⟨(3 / 4 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 106 ⟨(3 / 4 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (1) true (by convert Leaf8.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf8.box]) (by convert Leaf9.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf9.box])

fc_compact_decl theorem node5 : Excludes 106 ⟨(1 / 2 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 106 ⟨(1 / 2 : ℚ), (1 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (1) false (by convert Leaf7.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf7.box]) (by convert node4 using 1 <;> norm_num [TBox.left, TBox.right])

fc_compact_decl theorem node6 : Excludes 106 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 106 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert node3 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert node5 using 1 <;> norm_num [TBox.left, TBox.right])

fc_compact_decl theorem node7 : Excludes 106 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 106 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert Leaf4.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf4.box]) (by convert node6 using 1 <;> norm_num [TBox.left, TBox.right])

fc_compact_decl theorem node8 : Excludes 106 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 106 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node2 node7

fc_compact_decl theorem excludes : Excludes 106 TBox.unit 0 := by
  simpa [TBox.unit] using node8

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case106


/- Generated compressed exclusion certificate. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSquares.CenterElimination.Compressed.Case107

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 107 ![![0, 0, 19456, 0], ![19456, 0, 0, 0], ![0, 13312, 0, 13312]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (0 : ℚ), (3211 / 16384 : ℚ), (247 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (3952 : ℚ), (-11115 : ℚ)], ![(3952 : ℚ), (6422 : ℚ), (11856 : ℚ)], ![(-12939 : ℚ), (-3952 : ℚ), (-17632 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, 1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩

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

fc_compact_decl theorem excludes : Excludes 107 box (-1) :=

  excludes_of_scaled_numerator 107 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 107 ![![0, 0, 20480, 0], ![20480, 0, 0, 0], ![0, 4096, 0, 20480]] ![36864, 24576, 45056]

fc_compact_decl def a : Seven := ![(521 / 1920 : ℚ), (9 / 16 : ℚ), (99 / 160 : ℚ), (3 / 8 : ℚ), (3 / 80 : ℚ), (11 / 32 : ℚ), (55 / 96 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-413 : ℚ), (4688 : ℚ), (-5933 : ℚ)], ![(352 : ℚ), (5280 : ℚ), (9152 : ℚ)], ![(-7373 : ℚ), (-4112 : ℚ), (-7613 : ℚ)]]

fc_compact_decl def scale : ℚ := 3840

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, 1]

fc_compact_decl def box : TBox := ⟨(0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩

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

fc_compact_decl theorem excludes : Excludes 107 box (-1) :=

  excludes_of_scaled_numerator 107 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 107 ⟨(0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) :=
  excludes_split 107 ⟨(0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) true (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box])

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 107 ![![0, 0, 10240, 10240], ![20480, 0, 0, 0], ![0, 8192, 0, 16384]] ![57344, 0, 61440]

fc_compact_decl def a : Seven := ![(-1037 / 1920 : ℚ), (7 / 8 : ℚ), (21 / 16 : ℚ), (0 : ℚ), (0 : ℚ), (15 / 16 : ℚ), (5 / 8 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-1489 : ℚ), (4800 : ℚ), (-8689 : ℚ)], ![(5280 : ℚ), (14400 : ℚ), (14880 : ℚ)], ![(-15409 : ℚ), (-4800 : ℚ), (-8209 : ℚ)]]

fc_compact_decl def scale : ℚ := 3840

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 107 box (-1) :=

  excludes_of_scaled_numerator 107 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

fc_compact_decl theorem node1 : Excludes 107 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) :=
  excludes_split 107 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) false (by convert node0 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box])

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 107 ![![0, 0, 13312, 13312], ![19456, 0, 0, 0], ![0, 0, 0, 19456]] ![31616, 31616, 38912]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (3211 / 16384 : ℚ), (57 / 512 : ℚ), (19 / 32 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-7163 : ℚ), (25878 : ℚ), (-18715 : ℚ)], ![(-3648 : ℚ), (7296 : ℚ), (35264 : ℚ)], ![(-26619 : ℚ), (-13034 : ℚ), (-30875 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 107 box (-1) :=

  excludes_of_scaled_numerator 107 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

namespace Leaf4

fc_compact_decl def cert : Certificate := mkCert 107 ![![0, 0, 10240, 10240], ![22528, 0, 0, 0], ![0, 0, 0, 22528]] ![55296, 0, 67584]

fc_compact_decl def a : Seven := ![(-9589 / 14080 : ℚ), (27 / 32 : ℚ), (81 / 64 : ℚ), (0 : ℚ), (0 : ℚ), (33 / 32 : ℚ), (33 / 32 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-1641 : ℚ), (7260 : ℚ), (-8901 : ℚ)], ![(1650 : ℚ), (14520 : ℚ), (16170 : ℚ)], ![(-14841 : ℚ), (-7260 : ℚ), (-7581 : ℚ)]]

fc_compact_decl def scale : ℚ := 3520

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 107 box (-1) :=

  excludes_of_scaled_numerator 107 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf4

fc_compact_decl theorem node2 : Excludes 107 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 107 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) false (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box]) (by convert Leaf4.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf4.box])

fc_compact_decl theorem node3 : Excludes 107 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 107 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) true (by convert node1 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert node2 using 1 <;> norm_num [TBox.left, TBox.right])

namespace Leaf5

fc_compact_decl def cert : Certificate := mkCert 107 ![![0, 0, 12288, 12288], ![16384, 0, 0, 0], ![0, 12288, 0, 12288]] ![61440, 0, 69632]

fc_compact_decl def a : Seven := ![(-445 / 384 : ℚ), (15 / 16 : ℚ), (255 / 128 : ℚ), (0 : ℚ), (0 : ℚ), (17 / 16 : ℚ), (17 / 32 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-629 : ℚ), (816 : ℚ), (-2261 : ℚ)], ![(2244 : ℚ), (3264 : ℚ), (3876 : ℚ)], ![(-3701 : ℚ), (-816 : ℚ), (-2069 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 107 box (-1) :=

  excludes_of_scaled_numerator 107 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf5

fc_compact_decl theorem node4 : Excludes 107 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 107 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert node3 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf5.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf5.box])

namespace Leaf6

fc_compact_decl def cert : Certificate := mkCert 107 ![![0, 0, 19456, 0], ![19456, 0, 0, 0], ![0, 13312, 0, 13312]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (0 : ℚ), (3211 / 16384 : ℚ), (-247 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (-3952 : ℚ), (-11115 : ℚ)], ![(11856 : ℚ), (6422 : ℚ), (3952 : ℚ)], ![(-12939 : ℚ), (3952 : ℚ), (-17632 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 107 box (1) :=

  excludes_of_scaled_numerator 107 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf6

namespace Leaf7

fc_compact_decl def cert : Certificate := mkCert 107 ![![0, 0, 11264, 11264], ![18432, 0, 0, 0], ![0, 12288, 0, 12288]] ![58368, 0, 64512]

fc_compact_decl def a : Seven := ![(-16549 / 22528 : ℚ), (57 / 64 : ℚ), (399 / 256 : ℚ), (0 : ℚ), (0 : ℚ), (63 / 64 : ℚ), (-63 / 128 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-11709 : ℚ), (-22176 : ℚ), (-56061 : ℚ)], ![(92400 : ℚ), (88704 : ℚ), (48048 : ℚ)], ![(-96189 : ℚ), (22176 : ℚ), (-51837 : ℚ)]]

fc_compact_decl def scale : ℚ := 22528

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 107 box (1) :=

  excludes_of_scaled_numerator 107 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf7

fc_compact_decl theorem node5 : Excludes 107 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 107 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) false (by convert Leaf6.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf6.box]) (by convert Leaf7.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf7.box])

namespace Leaf8

fc_compact_decl def cert : Certificate := mkCert 107 ![![0, 0, 8192, 8192], ![16384, 0, 0, 0], ![0, 16384, 0, 16384]] ![65536, 0, 73728]

fc_compact_decl def a : Seven := ![(-203 / 128 : ℚ), (1 : ℚ), (9 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (9 / 8 : ℚ), (-9 / 16 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-287 : ℚ), (-288 : ℚ), (-863 : ℚ)], ![(1440 : ℚ), (1152 : ℚ), (864 : ℚ)], ![(-1375 : ℚ), (288 : ℚ), (-799 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 107 box (1) :=

  excludes_of_scaled_numerator 107 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf8

fc_compact_decl theorem node6 : Excludes 107 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 107 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert node5 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf8.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf8.box])

namespace Leaf9

fc_compact_decl def cert : Certificate := mkCert 107 ![![0, 0, 12288, 12288], ![12288, 0, 0, 0], ![0, 28672, 0, 0]] ![77824, 0, 90112]

fc_compact_decl def a : Seven := ![(-10121 / 2688 : ℚ), (19 / 16 : ℚ), (209 / 48 : ℚ), (0 : ℚ), (0 : ℚ), (11 / 8 : ℚ), (-11 / 8 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-15391 : ℚ), (-14784 : ℚ), (-30175 : ℚ)], ![(61600 : ℚ), (29568 : ℚ), (32032 : ℚ)], ![(-42943 : ℚ), (14784 : ℚ), (-28159 : ℚ)]]

fc_compact_decl def scale : ℚ := 5376

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 107 box (1) :=

  excludes_of_scaled_numerator 107 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf9

fc_compact_decl theorem node7 : Excludes 107 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 107 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert node6 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf9.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf9.box])

fc_compact_decl theorem node8 : Excludes 107 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 107 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node4 node7

fc_compact_decl theorem excludes : Excludes 107 TBox.unit 0 := by
  simpa [TBox.unit] using node8

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case107
