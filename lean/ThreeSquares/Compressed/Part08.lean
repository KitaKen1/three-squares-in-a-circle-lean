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

namespace ThreeSquares.CenterElimination.Compressed.Case096

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 96 ![![0, 0, 0, 24576], ![0, 0, 0, 8192], ![32768, 0, 0, 0]] ![57344, 49152, 57344]

fc_compact_decl def a : Seven := ![(-811 / 384 : ℚ), (49 / 16 : ℚ), (7 / 8 : ℚ), (3 / 4 : ℚ), (7 / 8 : ℚ), (7 / 8 : ℚ), (21 / 32 : ℚ)]

fc_compact_decl def n : Numerator := ![![(703 : ℚ), (2352 : ℚ), (-1793 : ℚ)], ![(336 : ℚ), (2688 : ℚ), (2352 : ℚ)], ![(-5345 : ℚ), (336 : ℚ), (-5153 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 96 box (-1) :=

  excludes_of_scaled_numerator 96 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 96 ![![0, 0, 0, 8192], ![0, 0, 0, 24576], ![32768, 0, 0, 0]] ![90112, 81920, 73728]

fc_compact_decl def a : Seven := ![(-2563 / 384 : ℚ), (33 / 16 : ℚ), (11 / 8 : ℚ), (5 / 4 : ℚ), (55 / 8 : ℚ), (9 / 8 : ℚ), (45 / 32 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-2993 : ℚ), (12720 : ℚ), (-6641 : ℚ)], ![(-48 : ℚ), (3456 : ℚ), (4272 : ℚ)], ![(-7889 : ℚ), (8400 : ℚ), (-8081 : ℚ)]]

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

fc_compact_decl theorem excludes : Excludes 96 box (-1) :=

  excludes_of_scaled_numerator 96 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 96 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 96 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box])

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 96 ![![0, 0, 0, 20480], ![0, 0, 0, 14336], ![30720, 0, 0, 0]] ![73728, 59392, 77824]

fc_compact_decl def a : Seven := ![(-72547 / 26880 : ℚ), (171 / 56 : ℚ), (9 / 8 : ℚ), (29 / 32 : ℚ), (261 / 160 : ℚ), (19 / 16 : ℚ), (-19 / 480 : ℚ)]

fc_compact_decl def n : Numerator := ![![(5297 : ℚ), (21392 : ℚ), (-22843 : ℚ)], ![(15652 : ℚ), (31920 : ℚ), (14588 : ℚ)], ![(-51703 : ℚ), (22456 : ℚ), (-47923 : ℚ)]]

fc_compact_decl def scale : ℚ := 6720

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

fc_compact_decl theorem excludes : Excludes 96 box (1) :=

  excludes_of_scaled_numerator 96 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 96 ![![0, 0, 0, 16384], ![0, 0, 0, 20480], ![28672, 0, 0, 0]] ![53248, 32768, 57344]

fc_compact_decl def a : Seven := ![(-795 / 1792 : ℚ), (91 / 80 : ℚ), (13 / 16 : ℚ), (1 / 2 : ℚ), (13 / 16 : ℚ), (7 / 8 : ℚ), (-3 / 8 : ℚ)]

fc_compact_decl def n : Numerator := ![![(1831 : ℚ), (3920 : ℚ), (-10489 : ℚ)], ![(10640 : ℚ), (15680 : ℚ), (3920 : ℚ)], ![(-16201 : ℚ), (10640 : ℚ), (-12841 : ℚ)]]

fc_compact_decl def scale : ℚ := 4480

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

fc_compact_decl theorem excludes : Excludes 96 box (1) :=

  excludes_of_scaled_numerator 96 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

namespace Leaf4

fc_compact_decl def cert : Certificate := mkCert 96 ![![0, 0, 0, 19456], ![0, 0, 0, 19456], ![13312, 0, 13312, 0]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (247 / 512 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (-3211 / 16384 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-1083 : ℚ), (9386 : ℚ), (-24795 : ℚ)], ![(25878 : ℚ), (15808 : ℚ), (13034 : ℚ)], ![(-24795 : ℚ), (22230 : ℚ), (-32699 : ℚ)]]

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

fc_compact_decl theorem excludes : Excludes 96 box (1) :=

  excludes_of_scaled_numerator 96 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf4

fc_compact_decl theorem node1 : Excludes 96 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 96 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) false (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box]) (by convert Leaf4.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf4.box])

namespace Leaf5

fc_compact_decl def cert : Certificate := mkCert 96 ![![0, 0, 0, 16384], ![0, 0, 0, 24576], ![24576, 0, 0, 0]] ![65536, 57344, 57344]

fc_compact_decl def a : Seven := ![(-233 / 192 : ℚ), (7 / 6 : ℚ), (1 : ℚ), (7 / 8 : ℚ), (7 / 4 : ℚ), (7 / 8 : ℚ), (7 / 48 : ℚ)]

fc_compact_decl def n : Numerator := ![![(33 : ℚ), (2912 : ℚ), (-2655 : ℚ)], ![(1312 : ℚ), (2688 : ℚ), (1760 : ℚ)], ![(-3103 : ℚ), (2464 : ℚ), (-3103 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

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

fc_compact_decl theorem excludes : Excludes 96 box (1) :=

  excludes_of_scaled_numerator 96 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf5

fc_compact_decl theorem node2 : Excludes 96 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 96 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert node1 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf5.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf5.box])

fc_compact_decl theorem node3 : Excludes 96 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 96 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box]) (by convert node2 using 1 <;> norm_num [TBox.left, TBox.right])

fc_compact_decl theorem node4 : Excludes 96 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 96 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node0 node3

fc_compact_decl theorem excludes : Excludes 96 TBox.unit 0 := by
  simpa [TBox.unit] using node4

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case096


/- Generated compressed exclusion certificate. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSquares.CenterElimination.Compressed.Case097

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 97 ![![0, 0, 0, 19456], ![13312, 13312, 0, 0], ![0, 0, 19456, 0]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (3211 / 16384 : ℚ), (247 / 1024 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (7904 : ℚ), (-17632 : ℚ)], ![(3952 : ℚ), (15808 : ℚ), (3952 : ℚ)], ![(-11115 : ℚ), (7904 : ℚ), (-12939 : ℚ)]]

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

fc_compact_decl theorem excludes : Excludes 97 box (-1) :=

  excludes_of_scaled_numerator 97 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 97 ![![0, 0, 0, 16384], ![8192, 20480, 0, 0], ![0, 0, 20480, 0]] ![49152, 45056, 24576]

fc_compact_decl def a : Seven := ![(-33 / 1280 : ℚ), (3 / 7 : ℚ), (15 / 28 : ℚ), (11 / 16 : ℚ), (33 / 32 : ℚ), (3 / 8 : ℚ), (-3 / 80 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-873 : ℚ), (8904 : ℚ), (-10393 : ℚ)], ![(5136 : ℚ), (6720 : ℚ), (4464 : ℚ)], ![(-8073 : ℚ), (9576 : ℚ), (-10873 : ℚ)]]

fc_compact_decl def scale : ℚ := 4480

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

fc_compact_decl theorem excludes : Excludes 97 box (-1) :=

  excludes_of_scaled_numerator 97 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 97 ⟨(0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) :=
  excludes_split 97 ⟨(0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) true (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box])

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 97 ![![0, 0, 0, 20480], ![0, 24576, 0, 0], ![0, 0, 20480, 0]] ![57344, 49152, 24576]

fc_compact_decl def a : Seven := ![(-11 / 48 : ℚ), (7 / 16 : ℚ), (7 / 8 : ℚ), (3 / 4 : ℚ), (21 / 20 : ℚ), (3 / 8 : ℚ), (-3 / 40 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-1255 : ℚ), (7488 : ℚ), (-9895 : ℚ)], ![(7296 : ℚ), (5760 : ℚ), (6144 : ℚ)], ![(-7495 : ℚ), (8640 : ℚ), (-10375 : ℚ)]]

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

fc_compact_decl theorem excludes : Excludes 97 box (-1) :=

  excludes_of_scaled_numerator 97 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

fc_compact_decl theorem node1 : Excludes 97 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) :=
  excludes_split 97 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) false (by convert node0 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box])

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 97 ![![0, 0, 0, 12288], ![4096, 24576, 0, 0], ![12288, 0, 12288, 0]] ![81920, 73728, 0]

fc_compact_decl def a : Seven := ![(-1003 / 336 : ℚ), (5 / 4 : ℚ), (15 / 14 : ℚ), (9 / 8 : ℚ), (15 / 4 : ℚ), (0 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-12205 : ℚ), (40320 : ℚ), (-24301 : ℚ)], ![(11520 : ℚ), (0 : ℚ), (11520 : ℚ)], ![(-25645 : ℚ), (40320 : ℚ), (-37741 : ℚ)]]

fc_compact_decl def scale : ℚ := 5376

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

fc_compact_decl theorem excludes : Excludes 97 box (-1) :=

  excludes_of_scaled_numerator 97 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

fc_compact_decl theorem node2 : Excludes 97 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 97 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) true (by convert node1 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box])

namespace Leaf4

fc_compact_decl def cert : Certificate := mkCert 97 ![![0, 0, 0, 16384], ![0, 28672, 0, 0], ![0, 0, 20480, 0]] ![69632, 61440, 28672]

fc_compact_decl def a : Seven := ![(-5291 / 4480 : ℚ), (17 / 32 : ℚ), (17 / 16 : ℚ), (15 / 16 : ℚ), (255 / 128 : ℚ), (7 / 16 : ℚ), (-7 / 32 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-8377 : ℚ), (31780 : ℚ), (-33017 : ℚ)], ![(22960 : ℚ), (15680 : ℚ), (15120 : ℚ)], ![(-25737 : ℚ), (39620 : ℚ), (-34697 : ℚ)]]

fc_compact_decl def scale : ℚ := 8960

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

fc_compact_decl theorem excludes : Excludes 97 box (-1) :=

  excludes_of_scaled_numerator 97 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf4

fc_compact_decl theorem node3 : Excludes 97 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 97 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert node2 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf4.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf4.box])

namespace Leaf5

fc_compact_decl def cert : Certificate := mkCert 97 ![![0, 0, 0, 19456], ![13312, 13312, 0, 0], ![0, 0, 19456, 0]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (3211 / 16384 : ℚ), (247 / 1024 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (-247 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (0 : ℚ), (-17632 : ℚ)], ![(11856 : ℚ), (15808 : ℚ), (-3952 : ℚ)], ![(-11115 : ℚ), (15808 : ℚ), (-12939 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

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

fc_compact_decl theorem excludes : Excludes 97 box (1) :=

  excludes_of_scaled_numerator 97 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf5

namespace Leaf6

fc_compact_decl def cert : Certificate := mkCert 97 ![![0, 0, 0, 16384], ![0, 32768, 0, 0], ![0, 0, 16384, 0]] ![65536, 65536, 49152]

fc_compact_decl def a : Seven := ![(-51 / 32 : ℚ), (1 / 4 : ℚ), (1 : ℚ), (1 : ℚ), (2 : ℚ), (3 / 4 : ℚ), (-3 / 2 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-321 : ℚ), (256 : ℚ), (-1217 : ℚ)], ![(1280 : ℚ), (768 : ℚ), (-256 : ℚ)], ![(-833 : ℚ), (1792 : ℚ), (-961 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

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

fc_compact_decl theorem excludes : Excludes 97 box (1) :=

  excludes_of_scaled_numerator 97 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf6

fc_compact_decl theorem node4 : Excludes 97 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 97 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert Leaf5.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf5.box]) (by convert Leaf6.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf6.box])

fc_compact_decl theorem node5 : Excludes 97 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 97 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node3 node4

fc_compact_decl theorem excludes : Excludes 97 TBox.unit 0 := by
  simpa [TBox.unit] using node5

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case097


/- Generated compressed exclusion certificate. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSquares.CenterElimination.Compressed.Case098

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 98 ![![0, 0, 32768, 0], ![0, 0, 0, 8192], ![0, 24576, 0, 0]] ![57344, 49152, 65536]

fc_compact_decl def a : Seven := ![(-1003 / 384 : ℚ), (7 / 2 : ℚ), (7 / 8 : ℚ), (3 / 4 : ℚ), (3 / 32 : ℚ), (1 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(751 : ℚ), (144 : ℚ), (-1937 : ℚ)], ![(1344 : ℚ), (3072 : ℚ), (1344 : ℚ)], ![(-6161 : ℚ), (144 : ℚ), (-5777 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

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

fc_compact_decl theorem excludes : Excludes 98 box (-1) :=

  excludes_of_scaled_numerator 98 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 98 ![![0, 0, 11428, 11428], ![0, 0, 0, 17024], ![0, 25656, 0, 0]] ![66369, 0, 78799]

fc_compact_decl def a : Seven := ![(-35461772572234031 / 20444699764457472 : ℚ), (747115833 / 318767104 : ℚ), (66369 / 65536 : ℚ), (0 : ℚ), (0 : ℚ), (78799 / 65536 : ℚ), (78799 / 65536 : ℚ)]

fc_compact_decl def n : Numerator := ![![(1548344079994193 : ℚ), (24582243297416448 : ℚ), (-23033899217422255 : ℚ)], ![(-3877679719119360 : ℚ), (49164486594832896 : ℚ), (45286806875713536 : ℚ)], ![(-70951512745565824 : ℚ), (-24582243297416448 : ℚ), (-46369269448149376 : ℚ)]]

fc_compact_decl def scale : ℚ := 10222349882228736

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

fc_compact_decl theorem excludes : Excludes 98 box (-1) :=

  excludes_of_scaled_numerator 98 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 98 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 98 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) true (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box])

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 98 ![![0, 0, 13312, 13312], ![0, 0, 0, 19456], ![0, 19456, 0, 0]] ![31616, 31616, 38912]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (3211 / 16384 : ℚ), (19 / 32 : ℚ), (57 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(741 : ℚ), (10070 : ℚ), (-26619 : ℚ)], ![(12160 : ℚ), (38912 : ℚ), (19456 : ℚ)], ![(-34523 : ℚ), (2774 : ℚ), (-22971 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

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

fc_compact_decl theorem excludes : Excludes 98 box (-1) :=

  excludes_of_scaled_numerator 98 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

fc_compact_decl theorem node1 : Excludes 98 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 98 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert node0 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box])

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 98 ![![0, 0, 32768, 0], ![0, 0, 0, 8192], ![0, 24576, 0, 0]] ![57344, 49152, 65536]

fc_compact_decl def a : Seven := ![(-1003 / 384 : ℚ), (7 / 2 : ℚ), (7 / 8 : ℚ), (3 / 4 : ℚ), (3 / 32 : ℚ), (1 : ℚ), (-1 : ℚ)]

fc_compact_decl def n : Numerator := ![![(751 : ℚ), (-1392 : ℚ), (-1937 : ℚ)], ![(2880 : ℚ), (3072 : ℚ), (-192 : ℚ)], ![(-6161 : ℚ), (1680 : ℚ), (-5777 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

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

fc_compact_decl theorem excludes : Excludes 98 box (1) :=

  excludes_of_scaled_numerator 98 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

namespace Leaf4

fc_compact_decl def cert : Certificate := mkCert 98 ![![0, 0, 32768, 0], ![0, 0, 0, 16384], ![0, 16384, 0, 0]] ![32768, 57344, 49152]

fc_compact_decl def a : Seven := ![(-67 / 128 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (7 / 8 : ℚ), (7 / 16 : ℚ), (3 / 4 : ℚ), (-21 / 16 : ℚ)]

fc_compact_decl def n : Numerator := ![![(49 : ℚ), (-448 : ℚ), (-783 : ℚ)], ![(928 : ℚ), (768 : ℚ), (-416 : ℚ)], ![(-719 : ℚ), (896 : ℚ), (-783 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 98 box (1) :=

  excludes_of_scaled_numerator 98 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf4

namespace Leaf5

fc_compact_decl def cert : Certificate := mkCert 98 ![![0, 0, 13312, 13312], ![0, 0, 0, 19456], ![0, 19456, 0, 0]] ![31616, 31616, 38912]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (3211 / 16384 : ℚ), (19 / 32 : ℚ), (-247 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(741 : ℚ), (-9386 : ℚ), (-26619 : ℚ)], ![(31616 : ℚ), (38912 : ℚ), (0 : ℚ)], ![(-34523 : ℚ), (22230 : ℚ), (-22971 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

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

fc_compact_decl theorem excludes : Excludes 98 box (1) :=

  excludes_of_scaled_numerator 98 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf5

fc_compact_decl theorem node2 : Excludes 98 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 98 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert Leaf4.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf4.box]) (by convert Leaf5.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf5.box])

fc_compact_decl theorem node3 : Excludes 98 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 98 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box]) (by convert node2 using 1 <;> norm_num [TBox.left, TBox.right])

fc_compact_decl theorem node4 : Excludes 98 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 98 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node1 node3

fc_compact_decl theorem excludes : Excludes 98 TBox.unit 0 := by
  simpa [TBox.unit] using node4

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case098


/- Generated compressed exclusion certificate. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSquares.CenterElimination.Compressed.Case099

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 99 ![![0, 0, 19456, 0], ![13312, 13312, 0, 0], ![0, 0, 0, 19456]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (3211 / 16384 : ℚ), (247 / 1024 : ℚ), (19 / 32 : ℚ), (57 / 512 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (9728 : ℚ), (-17632 : ℚ)], ![(-3952 : ℚ), (15808 : ℚ), (11856 : ℚ)], ![(-11115 : ℚ), (-6080 : ℚ), (-12939 : ℚ)]]

fc_compact_decl def scale : ℚ := 8192

fc_compact_decl def sigma : Fin 3 → ℚ := ![1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 99 box (-1) :=

  excludes_of_scaled_numerator 99 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 99 ![![0, 0, 24576, 0], ![8192, 16384, 0, 0], ![0, 0, 0, 16384]] ![24576, 40960, 32768]

fc_compact_decl def a : Seven := ![(21 / 64 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (5 / 8 : ℚ), (5 / 16 : ℚ), (1 / 2 : ℚ), (5 / 8 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-21 : ℚ), (480 : ℚ), (-597 : ℚ)], ![(-192 : ℚ), (512 : ℚ), (448 : ℚ)], ![(-341 : ℚ), (-160 : ℚ), (-405 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

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

fc_compact_decl theorem excludes : Excludes 99 box (-1) :=

  excludes_of_scaled_numerator 99 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 99 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) :=
  excludes_split 99 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) false (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box])

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 99 ![![0, 0, 24576, 0], ![12288, 12288, 0, 0], ![0, 0, 0, 16384]] ![0, 77824, 65536]

fc_compact_decl def a : Seven := ![(-1333 / 768 : ℚ), (0 : ℚ), (0 : ℚ), (19 / 16 : ℚ), (19 / 16 : ℚ), (1 : ℚ), (19 / 8 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-29 : ℚ), (171 : ℚ), (-134 : ℚ)], ![(-114 : ℚ), (96 : ℚ), (114 : ℚ)], ![(-77 : ℚ), (-57 : ℚ), (-86 : ℚ)]]

fc_compact_decl def scale : ℚ := 24

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

fc_compact_decl theorem excludes : Excludes 99 box (-1) :=

  excludes_of_scaled_numerator 99 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 99 ![![0, 0, 24576, 0], ![8192, 8192, 0, 0], ![0, 0, 0, 24576]] ![0, 65536, 49152]

fc_compact_decl def a : Seven := ![(-11 / 24 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (1 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-283 : ℚ), (3072 : ℚ), (-2971 : ℚ)], ![(-1536 : ℚ), (2304 : ℚ), (1536 : ℚ)], ![(-1435 : ℚ), (0 : ℚ), (-1819 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

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

fc_compact_decl theorem excludes : Excludes 99 box (-1) :=

  excludes_of_scaled_numerator 99 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

fc_compact_decl theorem node1 : Excludes 99 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 99 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) false (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box]) (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box])

fc_compact_decl theorem node2 : Excludes 99 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 99 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) true (by convert node0 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert node1 using 1 <;> norm_num [TBox.left, TBox.right])

namespace Leaf4

fc_compact_decl def cert : Certificate := mkCert 99 ![![0, 0, 13312, 13312], ![0, 19456, 0, 0], ![0, 0, 0, 19456]] ![31616, 31616, 38912]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (0 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (3211 / 16384 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-7163 : ℚ), (22230 : ℚ), (-34523 : ℚ)], ![(0 : ℚ), (38912 : ℚ), (31616 : ℚ)], ![(-26619 : ℚ), (-9386 : ℚ), (-15067 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

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

fc_compact_decl theorem excludes : Excludes 99 box (-1) :=

  excludes_of_scaled_numerator 99 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf4

fc_compact_decl theorem node3 : Excludes 99 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 99 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert node2 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf4.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf4.box])

namespace Leaf5

fc_compact_decl def cert : Certificate := mkCert 99 ![![0, 0, 19456, 0], ![13312, 13312, 0, 0], ![0, 0, 0, 19456]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (3211 / 16384 : ℚ), (247 / 1024 : ℚ), (19 / 32 : ℚ), (57 / 512 : ℚ), (247 / 512 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (1824 : ℚ), (-17632 : ℚ)], ![(3952 : ℚ), (15808 : ℚ), (3952 : ℚ)], ![(-11115 : ℚ), (1824 : ℚ), (-12939 : ℚ)]]

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

fc_compact_decl theorem excludes : Excludes 99 box (1) :=

  excludes_of_scaled_numerator 99 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf5

namespace Leaf6

fc_compact_decl def cert : Certificate := mkCert 99 ![![0, 0, 20480, 0], ![0, 24576, 0, 0], ![0, 0, 0, 20480]] ![40960, 32768, 28672]

fc_compact_decl def a : Seven := ![(593 / 1920 : ℚ), (25 / 96 : ℚ), (5 / 8 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (7 / 16 : ℚ), (-7 / 80 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-589 : ℚ), (-672 : ℚ), (-7789 : ℚ)], ![(5472 : ℚ), (6720 : ℚ), (4128 : ℚ)], ![(-5949 : ℚ), (672 : ℚ), (-6429 : ℚ)]]

fc_compact_decl def scale : ℚ := 3840

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

fc_compact_decl theorem excludes : Excludes 99 box (1) :=

  excludes_of_scaled_numerator 99 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf6

fc_compact_decl theorem node4 : Excludes 99 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 99 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) false (by convert Leaf5.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf5.box]) (by convert Leaf6.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf6.box])

namespace Leaf7

fc_compact_decl def cert : Certificate := mkCert 99 ![![0, 0, 24576, 0], ![0, 16384, 0, 0], ![0, 0, 0, 24576]] ![24576, 49152, 32768]

fc_compact_decl def a : Seven := ![(43 / 192 : ℚ), (0 : ℚ), (3 / 8 : ℚ), (3 / 4 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-143 : ℚ), (576 : ℚ), (-2063 : ℚ)], ![(576 : ℚ), (1536 : ℚ), (576 : ℚ)], ![(-911 : ℚ), (576 : ℚ), (-1295 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

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

fc_compact_decl theorem excludes : Excludes 99 box (1) :=

  excludes_of_scaled_numerator 99 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf7

fc_compact_decl theorem node5 : Excludes 99 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 99 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert node4 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf7.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf7.box])

namespace Leaf8

fc_compact_decl def cert : Certificate := mkCert 99 ![![0, 0, 20480, 0], ![0, 24576, 0, 0], ![0, 0, 0, 20480]] ![40960, 28672, 36864]

fc_compact_decl def a : Seven := ![(541 / 1920 : ℚ), (5 / 32 : ℚ), (5 / 8 : ℚ), (7 / 16 : ℚ), (0 : ℚ), (9 / 16 : ℚ), (-27 / 160 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-853 : ℚ), (-1296 : ℚ), (-8533 : ℚ)], ![(6096 : ℚ), (8640 : ℚ), (3504 : ℚ)], ![(-6373 : ℚ), (1296 : ℚ), (-5413 : ℚ)]]

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

fc_compact_decl theorem excludes : Excludes 99 box (1) :=

  excludes_of_scaled_numerator 99 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf8

namespace Leaf9

fc_compact_decl def cert : Certificate := mkCert 99 ![![0, 0, 19456, 0], ![0, 19456, 0, 0], ![0, 13312, 0, 13312]] ![38912, 31616, 31616]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (57 / 512 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (0 : ℚ), (247 / 1024 : ℚ), (-3211 / 16384 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-7163 : ℚ), (-6422 : ℚ), (-30875 : ℚ)], ![(25878 : ℚ), (15808 : ℚ), (13034 : ℚ)], ![(-18715 : ℚ), (6422 : ℚ), (-26619 : ℚ)]]

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

fc_compact_decl theorem excludes : Excludes 99 box (1) :=

  excludes_of_scaled_numerator 99 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf9

namespace Leaf10

fc_compact_decl def cert : Certificate := mkCert 99 ![![0, 0, 20480, 0], ![0, 20480, 0, 0], ![0, 0, 0, 24576]] ![32768, 28672, 40960]

fc_compact_decl def a : Seven := ![(593 / 1920 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (7 / 16 : ℚ), (7 / 80 : ℚ), (5 / 8 : ℚ), (-25 / 96 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-1109 : ℚ), (-1328 : ℚ), (-9269 : ℚ)], ![(5840 : ℚ), (9600 : ℚ), (1840 : ℚ)], ![(-5909 : ℚ), (2672 : ℚ), (-4469 : ℚ)]]

fc_compact_decl def scale : ℚ := 3840

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

fc_compact_decl theorem excludes : Excludes 99 box (1) :=

  excludes_of_scaled_numerator 99 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf10

fc_compact_decl theorem node6 : Excludes 99 ⟨(3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 99 ⟨(3 / 4 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) true (by convert Leaf9.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf9.box]) (by convert Leaf10.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf10.box])

fc_compact_decl theorem node7 : Excludes 99 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 99 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) false (by convert Leaf8.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf8.box]) (by convert node6 using 1 <;> norm_num [TBox.left, TBox.right])

namespace Leaf11

fc_compact_decl def cert : Certificate := mkCert 99 ![![0, 0, 13312, 13312], ![0, 19456, 0, 0], ![0, 0, 0, 19456]] ![31616, 31616, 38912]

fc_compact_decl def a : Seven := ![(6357 / 16384 : ℚ), (0 : ℚ), (247 / 512 : ℚ), (247 / 1024 : ℚ), (3211 / 16384 : ℚ), (19 / 32 : ℚ), (-57 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-7163 : ℚ), (2774 : ℚ), (-34523 : ℚ)], ![(19456 : ℚ), (38912 : ℚ), (12160 : ℚ)], ![(-26619 : ℚ), (10070 : ℚ), (-15067 : ℚ)]]

fc_compact_decl def scale : ℚ := 16384

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

fc_compact_decl theorem excludes : Excludes 99 box (1) :=

  excludes_of_scaled_numerator 99 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf11

fc_compact_decl theorem node8 : Excludes 99 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 99 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert node7 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf11.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf11.box])

fc_compact_decl theorem node9 : Excludes 99 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 99 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert node5 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert node8 using 1 <;> norm_num [TBox.left, TBox.right])

fc_compact_decl theorem node10 : Excludes 99 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 99 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node3 node9

fc_compact_decl theorem excludes : Excludes 99 TBox.unit 0 := by
  simpa [TBox.unit] using node10

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case099
