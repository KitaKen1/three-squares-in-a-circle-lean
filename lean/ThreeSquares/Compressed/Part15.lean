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

namespace ThreeSquares.CenterElimination.Compressed.Case360

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 360 ![![0, 0, 0, 19456], ![0, 19456, 0, 0], ![13312, 0, 13312, 0]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (19 / 32 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (0 : ℚ), (3211 / 16384 : ℚ), (741 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (11856 : ℚ), (-11115 : ℚ)], ![(-2128 : ℚ), (6422 : ℚ), (21584 : ℚ)], ![(-12939 : ℚ), (-11856 : ℚ), (-17632 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 360 box (-1) :=

  excludes_of_scaled_numerator 360 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 360 ![![0, 19456, 0, 0], ![0, 19456, 0, 0], ![13312, 0, 13312, 0]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (0 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (3211 / 16384 : ℚ), (741 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-4864 : ℚ), (19760 : ℚ), (-15979 : ℚ)], ![(-2128 : ℚ), (6422 : ℚ), (21584 : ℚ)], ![(-8075 : ℚ), (-3952 : ℚ), (-12768 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 360 box (-1) :=

  excludes_of_scaled_numerator 360 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 360 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 360 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box])

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 360 ![![0, 0, 0, 19456], ![0, 19456, 0, 0], ![13312, 0, 13312, 0]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (19 / 32 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (0 : ℚ), (3211 / 16384 : ℚ), (247 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (3952 : ℚ), (-11115 : ℚ)], ![(5776 : ℚ), (6422 : ℚ), (13680 : ℚ)], ![(-12939 : ℚ), (-3952 : ℚ), (-17632 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 360 box (1) :=

  excludes_of_scaled_numerator 360 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 360 ![![0, 0, 0, 20480], ![0, 24576, 0, 0], ![4096, 0, 16384, 0]] ![53248, 12288, 40960]

fc_compact_decl def a : Seven := ![(149 / 1920 : ℚ), (13 / 16 : ℚ), (13 / 16 : ℚ), (3 / 16 : ℚ), (0 : ℚ), (7 / 16 : ℚ), (-41 / 160 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-557 : ℚ), (-1968 : ℚ), (-5357 : ℚ)], ![(8208 : ℚ), (6720 : ℚ), (4272 : ℚ)], ![(-10157 : ℚ), (1968 : ℚ), (-8237 : ℚ)]]

fc_compact_decl def scale : ℚ := 3840

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 360 box (1) :=

  excludes_of_scaled_numerator 360 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

fc_compact_decl theorem node1 : Excludes 360 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 360 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) false (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box]) (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box])

namespace Leaf4

fc_compact_decl def cert : Certificate := mkCert 360 ![![0, 20480, 0, 0], ![0, 12288, 0, 0], ![16384, 0, 16384, 0]] ![32768, 53248, 20480]

fc_compact_decl def a : Seven := ![(689 / 3840 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (13 / 16 : ℚ), (13 / 16 : ℚ), (15 / 256 : ℚ), (79 / 160 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-2341 : ℚ), (10032 : ℚ), (-9031 : ℚ)], ![(48 : ℚ), (900 : ℚ), (7632 : ℚ)], ![(-2791 : ℚ), (2448 : ℚ), (-8581 : ℚ)]]

fc_compact_decl def scale : ℚ := 3840

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 360 box (1) :=

  excludes_of_scaled_numerator 360 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf4

fc_compact_decl theorem node2 : Excludes 360 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 360 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert node1 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf4.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf4.box])

namespace Leaf5

fc_compact_decl def cert : Certificate := mkCert 360 ![![0, 0, 0, 20480], ![0, 26624, 0, 0], ![2048, 0, 16384, 0]] ![53248, 4096, 47104]

fc_compact_decl def a : Seven := ![(-241 / 2496 : ℚ), (13 / 16 : ℚ), (13 / 16 : ℚ), (1 / 16 : ℚ), (0 : ℚ), (23 / 36 : ℚ), (-803 / 1440 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-36365 : ℚ), (-167024 : ℚ), (-246445 : ℚ)], ![(410384 : ℚ), (382720 : ℚ), (76336 : ℚ)], ![(-471085 : ℚ), (167024 : ℚ), (-298445 : ℚ)]]

fc_compact_decl def scale : ℚ := 149760

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 360 box (1) :=

  excludes_of_scaled_numerator 360 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf5

namespace Leaf6

fc_compact_decl def cert : Certificate := mkCert 360 ![![0, 13312, 0, 13312], ![0, 19456, 0, 0], ![0, 0, 19456, 0]] ![31616, 31616, 38912]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (247 / 1024 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (57 / 512 : ℚ), (-5035 / 16384 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-7163 : ℚ), (-2166 : ℚ), (-26619 : ℚ)], ![(25878 : ℚ), (7296 : ℚ), (5738 : ℚ)], ![(-18715 : ℚ), (17974 : ℚ), (-30875 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 360 box (1) :=

  excludes_of_scaled_numerator 360 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf6

namespace Leaf7

fc_compact_decl def cert : Certificate := mkCert 360 ![![0, 16384, 0, 4096], ![0, 20480, 0, 0], ![0, 0, 24576, 0]] ![32768, 20480, 49152]

fc_compact_decl def a : Seven := ![(469 / 1920 : ℚ), (1 / 10 : ℚ), (1 / 2 : ℚ), (5 / 16 : ℚ), (1 / 4 : ℚ), (7 / 16 : ℚ), (-1 / 2 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-2173 : ℚ), (-1920 : ℚ), (-7933 : ℚ)], ![(7680 : ℚ), (6720 : ℚ), (0 : ℚ)], ![(-6301 : ℚ), (5760 : ℚ), (-5341 : ℚ)]]

fc_compact_decl def scale : ℚ := 3840

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 360 box (1) :=

  excludes_of_scaled_numerator 360 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf7

fc_compact_decl theorem node3 : Excludes 360 ⟨(3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 360 ⟨(3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) true (by convert Leaf6.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf6.box]) (by convert Leaf7.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf7.box])

fc_compact_decl theorem node4 : Excludes 360 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 360 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) false (by convert Leaf5.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf5.box]) (by convert node3 using 1 <;> norm_num [TBox.left, TBox.right])

namespace Leaf8

fc_compact_decl def cert : Certificate := mkCert 360 ![![0, 19456, 0, 0], ![0, 19456, 0, 0], ![13312, 0, 13312, 0]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (0 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (3211 / 16384 : ℚ), (247 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-4864 : ℚ), (11856 : ℚ), (-15979 : ℚ)], ![(5776 : ℚ), (6422 : ℚ), (13680 : ℚ)], ![(-8075 : ℚ), (3952 : ℚ), (-12768 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 360 box (1) :=

  excludes_of_scaled_numerator 360 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf8

fc_compact_decl theorem node5 : Excludes 360 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 360 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert node4 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf8.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf8.box])

fc_compact_decl theorem node6 : Excludes 360 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 360 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert node2 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert node5 using 1 <;> norm_num [TBox.left, TBox.right])

fc_compact_decl theorem node7 : Excludes 360 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 360 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node0 node6

fc_compact_decl theorem excludes : Excludes 360 TBox.unit 0 := by
  simpa [TBox.unit] using node7

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case360


/- Generated compressed exclusion certificate. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSquares.CenterElimination.Compressed.Case361

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 361 ![![0, 4096, 0, 20480], ![28672, 0, 0, 0], ![0, 0, 12288, 0]] ![40960, 45056, 40960]

fc_compact_decl def a : Seven := ![(-493 / 2688 : ℚ), (25 / 48 : ℚ), (5 / 8 : ℚ), (11 / 16 : ℚ), (11 / 96 : ℚ), (55 / 48 : ℚ), (115 / 96 : ℚ)]

fc_compact_decl def n : Numerator := ![![(2745 : ℚ), (14112 : ℚ), (-16967 : ℚ)], ![(-6160 : ℚ), (24640 : ℚ), (19600 : ℚ)], ![(-15175 : ℚ), (-11648 : ℚ), (-10247 : ℚ)]]

fc_compact_decl def scale : ℚ := 5376

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 361 box (-1) :=

  excludes_of_scaled_numerator 361 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 361 ![![0, 16384, 0, 0], ![24576, 0, 0, 0], ![0, 0, 24576, 0]] ![40960, 49152, 40960]

fc_compact_decl def a : Seven := ![(-7 / 64 : ℚ), (0 : ℚ), (5 / 8 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (5 / 8 : ℚ), (25 / 16 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-101 : ℚ), (1184 : ℚ), (-805 : ℚ)], ![(-480 : ℚ), (640 : ℚ), (1120 : ℚ)], ![(-421 : ℚ), (-416 : ℚ), (-485 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 361 box (-1) :=

  excludes_of_scaled_numerator 361 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 361 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 361 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) true (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box])

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 361 ![![0, 24576, 0, 0], ![32768, 0, 0, 0], ![0, 0, 8192, 0]] ![32768, 49152, 49152]

fc_compact_decl def a : Seven := ![(-115 / 96 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (9 / 4 : ℚ), (5 / 4 : ℚ)]

fc_compact_decl def n : Numerator := ![![(109 : ℚ), (3072 : ℚ), (-4499 : ℚ)], ![(-1152 : ℚ), (6912 : ℚ), (2688 : ℚ)], ![(-3347 : ℚ), (-768 : ℚ), (-1043 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 361 box (-1) :=

  excludes_of_scaled_numerator 361 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

fc_compact_decl theorem node1 : Excludes 361 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 361 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert node0 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box])

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 361 ![![0, 8192, 0, 24576], ![24576, 0, 0, 0], ![8192, 0, 0, 0]] ![24576, 32768, 32768]

fc_compact_decl def a : Seven := ![(5 / 384 : ℚ), (9 / 32 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (1 / 8 : ℚ), (1 : ℚ), (-5 / 16 : ℚ)]

fc_compact_decl def n : Numerator := ![![(103 : ℚ), (-288 : ℚ), (-2201 : ℚ)], ![(1056 : ℚ), (3072 : ℚ), (96 : ℚ)], ![(-1865 : ℚ), (672 : ℚ), (-1097 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 361 box (1) :=

  excludes_of_scaled_numerator 361 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

namespace Leaf4

fc_compact_decl def cert : Certificate := mkCert 361 ![![0, 16384, 0, 16384], ![16384, 0, 0, 0], ![16384, 0, 0, 0]] ![32768, 57344, 49152]

fc_compact_decl def a : Seven := ![(-51 / 128 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (7 / 8 : ℚ), (7 / 16 : ℚ), (21 / 16 : ℚ), (-5 / 16 : ℚ)]

fc_compact_decl def n : Numerator := ![![(97 : ℚ), (64 : ℚ), (-1023 : ℚ)], ![(416 : ℚ), (1344 : ℚ), (96 : ℚ)], ![(-703 : ℚ), (384 : ℚ), (-479 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 361 box (1) :=

  excludes_of_scaled_numerator 361 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf4

namespace Leaf5

fc_compact_decl def cert : Certificate := mkCert 361 ![![0, 13312, 0, 13312], ![19456, 0, 0, 0], ![19456, 0, 0, 0]] ![31616, 31616, 38912]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (247 / 1024 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (247 / 512 : ℚ), (-5035 / 16384 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-1083 : ℚ), (-2166 : ℚ), (-32699 : ℚ)], ![(25878 : ℚ), (31616 : ℚ), (5738 : ℚ)], ![(-24795 : ℚ), (17974 : ℚ), (-24795 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 361 box (1) :=

  excludes_of_scaled_numerator 361 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf5

fc_compact_decl theorem node2 : Excludes 361 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 361 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) false (by convert Leaf4.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf4.box]) (by convert Leaf5.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf5.box])

namespace Leaf6

fc_compact_decl def cert : Certificate := mkCert 361 ![![0, 32768, 0, 0], ![28672, 0, 0, 0], ![4096, 0, 0, 0]] ![28672, 49152, 45056]

fc_compact_decl def a : Seven := ![(-10831 / 3584 : ℚ), (0 : ℚ), (7 / 16 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (33 / 8 : ℚ), (-23 / 64 : ℚ)]

fc_compact_decl def n : Numerator := ![![(691 : ℚ), (2800 : ℚ), (-34253 : ℚ)], ![(5712 : ℚ), (59136 : ℚ), (560 : ℚ)], ![(-28877 : ℚ), (7952 : ℚ), (-4685 : ℚ)]]

fc_compact_decl def scale : ℚ := 3584

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 361 box (1) :=

  excludes_of_scaled_numerator 361 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf6

fc_compact_decl theorem node3 : Excludes 361 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 361 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert node2 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf6.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf6.box])

fc_compact_decl theorem node4 : Excludes 361 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 361 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box]) (by convert node3 using 1 <;> norm_num [TBox.left, TBox.right])

fc_compact_decl theorem node5 : Excludes 361 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 361 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node1 node4

fc_compact_decl theorem excludes : Excludes 361 TBox.unit 0 := by
  simpa [TBox.unit] using node5

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case361


/- Generated compressed exclusion certificate. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSquares.CenterElimination.Compressed.Case362

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 362 ![![0, 0, 28672, 0], ![0, 24576, 0, 0], ![0, 12288, 0, 0]] ![16384, 40960, 36864]

fc_compact_decl def a : Seven := ![(-15 / 896 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (5 / 8 : ℚ), (5 / 8 : ℚ), (15 / 16 : ℚ), (43 / 112 : ℚ)]

fc_compact_decl def n : Numerator := ![![(243 : ℚ), (3616 : ℚ), (-5357 : ℚ)], ![(-1376 : ℚ), (6720 : ℚ), (1376 : ℚ)], ![(-4013 : ℚ), (864 : ℚ), (-2893 : ℚ)]]

fc_compact_decl def scale : ℚ := 1792

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 362 box (-1) :=

  excludes_of_scaled_numerator 362 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 362 ![![0, 0, 13312, 13312], ![0, 19456, 0, 0], ![0, 19456, 0, 0]] ![31616, 31616, 38912]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (247 / 1024 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (5035 / 16384 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-1083 : ℚ), (25878 : ℚ), (-24795 : ℚ)], ![(-2166 : ℚ), (31616 : ℚ), (17974 : ℚ)], ![(-32699 : ℚ), (5738 : ℚ), (-24795 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 362 box (-1) :=

  excludes_of_scaled_numerator 362 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 362 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 362 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) true (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box])

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 362 ![![0, 0, 0, 32768], ![0, 28672, 0, 0], ![0, 4096, 0, 0]] ![32768, 40960, 40960]

fc_compact_decl def a : Seven := ![(-1847 / 896 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (5 / 8 : ℚ), (25 / 8 : ℚ), (5 / 16 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-173 : ℚ), (3360 : ℚ), (-11373 : ℚ)], ![(672 : ℚ), (22400 : ℚ), (2912 : ℚ)], ![(-13165 : ℚ), (1120 : ℚ), (-1965 : ℚ)]]

fc_compact_decl def scale : ℚ := 1792

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 362 box (-1) :=

  excludes_of_scaled_numerator 362 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

fc_compact_decl theorem node1 : Excludes 362 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 362 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert node0 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box])

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 362 ![![0, 0, 24576, 0], ![0, 28672, 0, 0], ![0, 0, 0, 12288]] ![36864, 49152, 45056]

fc_compact_decl def a : Seven := ![(-1121 / 2688 : ℚ), (9 / 16 : ℚ), (0 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (11 / 8 : ℚ), (-5 / 4 : ℚ)]

fc_compact_decl def n : Numerator := ![![(3281 : ℚ), (-5376 : ℚ), (-19567 : ℚ)], ![(13440 : ℚ), (29568 : ℚ), (-13440 : ℚ)], ![(-17551 : ℚ), (21504 : ℚ), (-10831 : ℚ)]]

fc_compact_decl def scale : ℚ := 5376

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 362 box (1) :=

  excludes_of_scaled_numerator 362 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

namespace Leaf4

fc_compact_decl def cert : Certificate := mkCert 362 ![![0, 0, 3320, 11355], ![0, 30702, 0, 0], ![0, 0, 0, 20159]] ![42737, 43454, 37358]

fc_compact_decl def a : Seven := ![(-29981478689635351 / 476193737626091520 : ℚ), (42737 / 65536 : ℚ), (97055727 / 192348160 : ℚ), (1803341 / 12021760 : ℚ), (21727 / 32768 : ℚ), (405838633 / 660570112 : ℚ), (-1476775449 / 961740800 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-730051031294097995 : ℚ), (-4154637615883699056 : ℚ), (-4369993688584507115 : ℚ)], ![(9714861506182303296 : ℚ), (5851243100787873600 : ℚ), (-4909270498901800416 : ℚ)], ![(-6761002746013943195 : ℚ), (10469494389200404656 : ℚ), (-4549702302516478715 : ℚ)]]

fc_compact_decl def scale : ℚ := 2380968688130457600

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 362 box (1) :=

  excludes_of_scaled_numerator 362 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf4

fc_compact_decl theorem node2 : Excludes 362 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 362 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box]) (by convert Leaf4.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf4.box])

fc_compact_decl theorem node3 : Excludes 362 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 362 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node1 node2

fc_compact_decl theorem excludes : Excludes 362 TBox.unit 0 := by
  simpa [TBox.unit] using node3

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case362


/- Generated compressed exclusion certificate. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSquares.CenterElimination.Compressed.Case363

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 363 ![![0, 0, 19456, 0], ![19456, 0, 0, 0], ![0, 13312, 0, 13312]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (19 / 32 : ℚ), (0 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (3211 / 16384 : ℚ), (-247 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (3952 : ℚ), (-11115 : ℚ)], ![(3952 : ℚ), (6422 : ℚ), (-3952 : ℚ)], ![(-12939 : ℚ), (11856 : ℚ), (-17632 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 363 box (-1) :=

  excludes_of_scaled_numerator 363 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 363 ![![0, 0, 20480, 0], ![18432, 0, 0, 0], ![0, 4096, 0, 22528]] ![30720, 32768, 36864]

fc_compact_decl def a : Seven := ![(6377 / 16640 : ℚ), (15 / 32 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (45 / 208 : ℚ), (21 / 208 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-191 : ℚ), (2500 : ℚ), (-3171 : ℚ)], ![(-420 : ℚ), (1800 : ℚ), (420 : ℚ)], ![(-3041 : ℚ), (1660 : ℚ), (-4221 : ℚ)]]

fc_compact_decl def scale : ℚ := 2080

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 363 box (-1) :=

  excludes_of_scaled_numerator 363 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 363 ⟨(0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) :=
  excludes_split 363 ⟨(0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) true (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box])

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 363 ![![0, 0, 22343, 0], ![14181, 0, 0, 0], ![0, 14506, 0, 14506]] ![31613, 51093, 21326]

fc_compact_decl def a : Seven := ![(692857676592310549 / 2409716399471591424 : ℚ), (31613 / 65536 : ℚ), (0 : ℚ), (51093 / 65536 : ℚ), (51093 / 65536 : ℚ), (73905253 / 1901330432 : ℚ), (-1138716191 / 2928541696 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-172935493241135951 : ℚ), (1883354542590149616 : ℚ), (-4117581445017532967 : ℚ)], ![(1873958689776855408 : ℚ), (374665438818783984 : ℚ), (-1873958689776855408 : ℚ)], ![(-2685047403827756327 : ℚ), (5631271922143860432 : ℚ), (-6255027916785369359 : ℚ)]]

fc_compact_decl def scale : ℚ := 2409716399471591424

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 363 box (-1) :=

  excludes_of_scaled_numerator 363 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

fc_compact_decl theorem node1 : Excludes 363 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) :=
  excludes_split 363 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) false (by convert node0 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box])

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 363 ![![0, 0, 13312, 13312], ![19456, 0, 0, 0], ![0, 0, 0, 19456]] ![31616, 31616, 38912]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (247 / 1024 : ℚ), (247 / 512 : ℚ), (57 / 512 : ℚ), (5035 / 16384 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-7163 : ℚ), (25878 : ℚ), (-18715 : ℚ)], ![(-2166 : ℚ), (7296 : ℚ), (17974 : ℚ)], ![(-26619 : ℚ), (5738 : ℚ), (-30875 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 363 box (-1) :=

  excludes_of_scaled_numerator 363 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

namespace Leaf4

fc_compact_decl def cert : Certificate := mkCert 363 ![![0, 0, 0, 20480], ![24576, 0, 0, 0], ![0, 0, 0, 20480]] ![53248, 4096, 49152]

fc_compact_decl def a : Seven := ![(-67 / 384 : ℚ), (13 / 16 : ℚ), (13 / 16 : ℚ), (0 : ℚ), (1 / 16 : ℚ), (27 / 40 : ℚ), (107 / 160 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-1333 : ℚ), (5616 : ℚ), (-6517 : ℚ)], ![(1104 : ℚ), (10368 : ℚ), (11376 : ℚ)], ![(-12757 : ℚ), (-4656 : ℚ), (-7573 : ℚ)]]

fc_compact_decl def scale : ℚ := 3840

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 363 box (-1) :=

  excludes_of_scaled_numerator 363 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf4

fc_compact_decl theorem node2 : Excludes 363 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 363 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) false (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box]) (by convert Leaf4.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf4.box])

fc_compact_decl theorem node3 : Excludes 363 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 363 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) true (by convert node1 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert node2 using 1 <;> norm_num [TBox.left, TBox.right])

namespace Leaf5

fc_compact_decl def cert : Certificate := mkCert 363 ![![0, 0, 0, 19456], ![19456, 0, 0, 0], ![0, 13312, 0, 13312]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (19 / 32 : ℚ), (19 / 32 : ℚ), (0 : ℚ), (247 / 512 : ℚ), (3211 / 16384 : ℚ), (-247 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-3952 : ℚ), (3952 : ℚ), (-7163 : ℚ)], ![(13680 : ℚ), (6422 : ℚ), (5776 : ℚ)], ![(-16891 : ℚ), (11856 : ℚ), (-13680 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 363 box (-1) :=

  excludes_of_scaled_numerator 363 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf5

fc_compact_decl theorem node4 : Excludes 363 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 363 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert node3 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf5.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf5.box])

namespace Leaf6

fc_compact_decl def cert : Certificate := mkCert 363 ![![0, 0, 19456, 0], ![19456, 0, 0, 0], ![0, 13312, 0, 13312]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (19 / 32 : ℚ), (0 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (3211 / 16384 : ℚ), (-741 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (-3952 : ℚ), (-11115 : ℚ)], ![(11856 : ℚ), (6422 : ℚ), (-11856 : ℚ)], ![(-12939 : ℚ), (19760 : ℚ), (-17632 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 363 box (1) :=

  excludes_of_scaled_numerator 363 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf6

namespace Leaf7

fc_compact_decl def cert : Certificate := mkCert 363 ![![0, 0, 0, 20480], ![24576, 0, 0, 0], ![0, 10240, 0, 10240]] ![53248, 16384, 34816]

fc_compact_decl def a : Seven := ![(1457 / 7680 : ℚ), (13 / 16 : ℚ), (13 / 16 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (51 / 160 : ℚ), (-189 / 320 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-2605 : ℚ), (-5232 : ℚ), (-7501 : ℚ)], ![(21552 : ℚ), (9792 : ℚ), (3408 : ℚ)], ![(-19981 : ℚ), (12912 : ℚ), (-15085 : ℚ)]]

fc_compact_decl def scale : ℚ := 7680

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 363 box (1) :=

  excludes_of_scaled_numerator 363 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf7

fc_compact_decl theorem node5 : Excludes 363 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 363 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) false (by convert Leaf6.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf6.box]) (by convert Leaf7.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf7.box])

namespace Leaf8

fc_compact_decl def cert : Certificate := mkCert 363 ![![0, 0, 0, 19456], ![19456, 0, 0, 0], ![0, 13312, 0, 13312]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (19 / 32 : ℚ), (19 / 32 : ℚ), (0 : ℚ), (247 / 512 : ℚ), (3211 / 16384 : ℚ), (-741 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-3952 : ℚ), (-3952 : ℚ), (-7163 : ℚ)], ![(21584 : ℚ), (6422 : ℚ), (-2128 : ℚ)], ![(-16891 : ℚ), (19760 : ℚ), (-13680 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 363 box (1) :=

  excludes_of_scaled_numerator 363 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf8

fc_compact_decl theorem node6 : Excludes 363 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 363 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert node5 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf8.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf8.box])

namespace Leaf9

fc_compact_decl def cert : Certificate := mkCert 363 ![![0, 0, 0, 19456], ![19456, 0, 0, 0], ![0, 13312, 0, 13312]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (19 / 32 : ℚ), (19 / 32 : ℚ), (0 : ℚ), (247 / 512 : ℚ), (3211 / 16384 : ℚ), (-741 / 1024 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-3952 : ℚ), (-3952 : ℚ), (-7163 : ℚ)], ![(21584 : ℚ), (6422 : ℚ), (-2128 : ℚ)], ![(-16891 : ℚ), (19760 : ℚ), (-13680 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 363 box (1) :=

  excludes_of_scaled_numerator 363 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf9

fc_compact_decl theorem node7 : Excludes 363 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 363 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert node6 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf9.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf9.box])

fc_compact_decl theorem node8 : Excludes 363 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 363 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node4 node7

fc_compact_decl theorem excludes : Excludes 363 TBox.unit 0 := by
  simpa [TBox.unit] using node8

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case363
