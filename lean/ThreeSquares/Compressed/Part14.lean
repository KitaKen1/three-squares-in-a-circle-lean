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

namespace ThreeSquares.CenterElimination.Compressed.Case352

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 352 ![![0, 0, 0, 32764], ![1, 1, 1, 1], ![32768, 0, 0, 0]] ![54935, 30840, 54935]

fc_compact_decl def a : Seven := ![(27067640661329 / 70360154243072 : ℚ), (54935 / 65536 : ℚ), (54935 / 65536 : ℚ), (3855 / 8192 : ℚ), (0 : ℚ), (54935 / 65536 : ℚ), (3469500404775 / 4397509640192 : ℚ)]

fc_compact_decl def n : Numerator := ![![(61326559757649 : ℚ), (111024012952800 : ℚ), (-122851364747951 : ℚ)], ![(6933600369440 : ℚ), (235915226644480 : ℚ), (228981626275040 : ℚ)], ![(-174588666886831 : ℚ), (-111024012952800 : ℚ), (-122851364747951 : ℚ)]]

fc_compact_decl def scale : ℚ := 70360154243072

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 352 box (-1) :=

  excludes_of_scaled_numerator 352 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 352 ![![0, 0, 0, 32764], ![1, 1, 1, 1], ![32768, 0, 0, 0]] ![54935, 30840, 54935]

fc_compact_decl def a : Seven := ![(27067640661329 / 70360154243072 : ℚ), (54935 / 65536 : ℚ), (54935 / 65536 : ℚ), (3855 / 8192 : ℚ), (0 : ℚ), (54935 / 65536 : ℚ), (-216675011545 / 4397509640192 : ℚ)]

fc_compact_decl def n : Numerator := ![![(61326559757649 : ℚ), (-6933600369440 : ℚ), (-122851364747951 : ℚ)], ![(124891213691680 : ℚ), (235915226644480 : ℚ), (111024012952800 : ℚ)], ![(-174588666886831 : ℚ), (6933600369440 : ℚ), (-122851364747951 : ℚ)]]

fc_compact_decl def scale : ℚ := 70360154243072

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 352 box (1) :=

  excludes_of_scaled_numerator 352 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 352 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 352 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) Leaf0.excludes Leaf1.excludes

fc_compact_decl theorem excludes : Excludes 352 TBox.unit 0 := by
  simpa [TBox.unit] using node0

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case352


/- Generated compressed exclusion certificate. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSquares.CenterElimination.Compressed.Case353

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 353 ![![0, 0, 0, 19456], ![13312, 13312, 0, 0], ![0, 0, 19456, 0]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(13 / 128 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (19 / 32 : ℚ), (0 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (247 : ℚ), (-551 : ℚ)], ![(0 : ℚ), (494 : ℚ), (494 : ℚ)], ![(-494 : ℚ), (-247 : ℚ), (-551 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

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

fc_compact_decl theorem excludes : Excludes 353 box (-1) :=

  excludes_of_scaled_numerator 353 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 353 ![![0, 0, 0, 19456], ![13312, 13312, 0, 0], ![0, 0, 19456, 0]] ![38912, 38912, 31616]

fc_compact_decl def a : Seven := ![(-11855 / 425984 : ℚ), (19 / 32 : ℚ), (19 / 32 : ℚ), (19 / 32 : ℚ), (0 : ℚ), (247 / 512 : ℚ), (19 / 32 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-7695 : ℚ), (505856 : ℚ), (-924559 : ℚ)], ![(0 : ℚ), (822016 : ℚ), (1011712 : ℚ)], ![(-924559 : ℚ), (-505856 : ℚ), (-1019407 : ℚ)]]

fc_compact_decl def scale : ℚ := 425984

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

fc_compact_decl theorem excludes : Excludes 353 box (-1) :=

  excludes_of_scaled_numerator 353 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 353 ⟨(0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) :=
  excludes_split 353 ⟨(0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) true (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box])

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 353 ![![0, 0, 0, 20480], ![16384, 16384, 0, 0], ![0, 0, 12288, 0]] ![49152, 32768, 20480]

fc_compact_decl def a : Seven := ![(73 / 7680 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (5 / 16 : ℚ), (119 / 240 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-677 : ℚ), (7616 : ℚ), (-13157 : ℚ)], ![(3904 : ℚ), (9600 : ℚ), (19136 : ℚ)], ![(-16997 : ℚ), (-7616 : ℚ), (-19877 : ℚ)]]

fc_compact_decl def scale : ℚ := 7680

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

fc_compact_decl theorem excludes : Excludes 353 box (-1) :=

  excludes_of_scaled_numerator 353 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

fc_compact_decl theorem node1 : Excludes 353 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) :=
  excludes_split 353 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (-1) false (by convert node0 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box])

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 353 ![![0, 18432, 0, 0], ![10240, 10240, 0, 0], ![13312, 0, 13312, 0]] ![56320, 71680, 0]

fc_compact_decl def a : Seven := ![(-109507 / 119808 : ℚ), (0 : ℚ), (55 / 64 : ℚ), (35 / 32 : ℚ), (35 / 32 : ℚ), (0 : ℚ), (1925 / 1152 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-177367 : ℚ), (662480 : ℚ), (-439447 : ℚ)], ![(-194480 : ℚ), (0 : ℚ), (606320 : ℚ)], ![(-177367 : ℚ), (-138320 : ℚ), (-439447 : ℚ)]]

fc_compact_decl def scale : ℚ := 119808

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

fc_compact_decl theorem excludes : Excludes 353 box (-1) :=

  excludes_of_scaled_numerator 353 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

namespace Leaf4

fc_compact_decl def cert : Certificate := mkCert 353 ![![0, 16384, 0, 0], ![12288, 12288, 0, 0], ![0, 0, 24576, 0]] ![32768, 49152, 28672]

fc_compact_decl def a : Seven := ![(-23 / 192 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (7 / 16 : ℚ), (3 / 4 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-455 : ℚ), (2304 : ℚ), (-2279 : ℚ)], ![(-384 : ℚ), (1344 : ℚ), (1920 : ℚ)], ![(-1127 : ℚ), (0 : ℚ), (-1607 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

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

fc_compact_decl theorem excludes : Excludes 353 box (-1) :=

  excludes_of_scaled_numerator 353 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf4

fc_compact_decl theorem node2 : Excludes 353 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 353 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) false (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box]) (by convert Leaf4.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf4.box])

fc_compact_decl theorem node3 : Excludes 353 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 353 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) true (by convert node1 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert node2 using 1 <;> norm_num [TBox.left, TBox.right])

namespace Leaf5

fc_compact_decl def cert : Certificate := mkCert 353 ![![0, 19456, 0, 0], ![13312, 13312, 0, 0], ![0, 0, 19456, 0]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(13 / 128 : ℚ), (0 : ℚ), (247 / 512 : ℚ), (19 / 32 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-247 : ℚ), (1102 : ℚ), (-1349 : ℚ)], ![(0 : ℚ), (988 : ℚ), (988 : ℚ)], ![(-741 : ℚ), (114 : ℚ), (-855 : ℚ)]]

fc_compact_decl def scale : ℚ := 512

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

fc_compact_decl theorem excludes : Excludes 353 box (-1) :=

  excludes_of_scaled_numerator 353 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf5

fc_compact_decl theorem node4 : Excludes 353 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 353 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert node3 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf5.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf5.box])

namespace Leaf6

fc_compact_decl def cert : Certificate := mkCert 353 ![![0, 0, 0, 19456], ![13312, 13312, 0, 0], ![0, 0, 19456, 0]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(13 / 128 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (19 / 32 : ℚ), (0 : ℚ), (247 / 512 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (0 : ℚ), (-551 : ℚ)], ![(247 : ℚ), (494 : ℚ), (247 : ℚ)], ![(-494 : ℚ), (0 : ℚ), (-551 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

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

fc_compact_decl theorem excludes : Excludes 353 box (1) :=

  excludes_of_scaled_numerator 353 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf6

namespace Leaf7

fc_compact_decl def cert : Certificate := mkCert 353 ![![0, 0, 0, 22523], ![14273, 14273, 0, 0], ![0, 0, 14467, 0]] ![43128, 34173, 28654]

fc_compact_decl def a : Seven := ![(-2797759495683 / 16475104816529408 : ℚ), (5391 / 8192 : ℚ), (5391 / 8192 : ℚ), (34173 / 65536 : ℚ), (0 : ℚ), (14327 / 32768 : ℚ), (-366356191509 / 21354266034176 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-26566101154562441 : ℚ), (-20916007685631828 : ℚ), (-1195328679932621685 : ℚ)], ![(823220629863041844 : ℚ), (1066093333512868976 : ℚ), (781388614491778188 : ℚ)], ![(-1361917390088406945 : ℚ), (20916007685631828 : ℚ), (-1464586635353597213 : ℚ)]]

fc_compact_decl def scale : ℚ := 609578878211588096

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

fc_compact_decl def box : TBox := ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 4 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ)⟩

fc_compact_decl theorem tri0_nonnegative (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v ≤ 1) : 0 ≤ numEval n (tri0.x u v) (tri0.y u v) :=
  triangle_nonnegative_of_coefficients n tri0 (by decide +kernel) u v hu hv hs

fc_compact_decl def tri1 : Triangle := ⟨(1 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)⟩

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

fc_compact_decl theorem excludes : Excludes 353 box (1) :=

  excludes_of_scaled_numerator 353 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf7

namespace Leaf8

fc_compact_decl def cert : Certificate := mkCert 353 ![![0, 20480, 0, 0], ![10240, 10240, 0, 0], ![0, 0, 24576, 0]] ![16384, 53248, 34816]

fc_compact_decl def a : Seven := ![(-35 / 1536 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (13 / 16 : ℚ), (13 / 16 : ℚ), (17 / 32 : ℚ), (-481 / 1920 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-2605 : ℚ), (8632 : ℚ), (-23245 : ℚ)], ![(7688 : ℚ), (16320 : ℚ), (-8 : ℚ)], ![(-10765 : ℚ), (16328 : ℚ), (-15085 : ℚ)]]

fc_compact_decl def scale : ℚ := 7680

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

fc_compact_decl def box : TBox := ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)⟩

fc_compact_decl theorem wellFormed : cert.wellFormed = true := by decide +kernel

fc_compact_decl theorem signs : ∀ e, sigma e = 1 ∨ sigma e = -1 ∨ sigma e = 0 := by
  intro e; fin_cases e <;> norm_num [sigma]

fc_compact_decl theorem coefficients : quadMatches (cert.lowerQuad sigma) a = true := by
  decide +kernel

fc_compact_decl theorem numerator_eq : n = fun i j => scale * numerator a i j := by
  have h : ∀ i j, n i j = scale * numerator a i j := by decide +kernel
  exact funext fun i => funext (h i)

fc_compact_decl def tri0 : Triangle := ⟨(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)⟩

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

fc_compact_decl theorem excludes : Excludes 353 box (1) :=

  excludes_of_scaled_numerator 353 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf8

fc_compact_decl theorem node5 : Excludes 353 ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 353 ⟨(1 / 4 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) true (by convert Leaf7.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf7.box]) (by convert Leaf8.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf8.box])

fc_compact_decl theorem node6 : Excludes 353 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 353 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) false (by convert Leaf6.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf6.box]) (by convert node5 using 1 <;> norm_num [TBox.left, TBox.right])

namespace Leaf9

fc_compact_decl def cert : Certificate := mkCert 353 ![![0, 19456, 0, 0], ![13312, 13312, 0, 0], ![0, 0, 19456, 0]] ![31616, 38912, 38912]

fc_compact_decl def a : Seven := ![(-11855 / 425984 : ℚ), (0 : ℚ), (247 / 512 : ℚ), (19 / 32 : ℚ), (19 / 32 : ℚ), (19 / 32 : ℚ), (-57 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-213199 : ℚ), (411008 : ℚ), (-1224911 : ℚ)], ![(505856 : ℚ), (1011712 : ℚ), (316160 : ℚ)], ![(-719055 : ℚ), (600704 : ℚ), (-719055 : ℚ)]]

fc_compact_decl def scale : ℚ := 425984

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

fc_compact_decl theorem excludes : Excludes 353 box (1) :=

  excludes_of_scaled_numerator 353 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf9

fc_compact_decl theorem node7 : Excludes 353 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 353 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert node6 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf9.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf9.box])

namespace Leaf10

fc_compact_decl def cert : Certificate := mkCert 353 ![![0, 24576, 0, 0], ![8192, 8192, 0, 0], ![0, 0, 24576, 0]] ![0, 65536, 49152]

fc_compact_decl def a : Seven := ![(-11 / 24 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (-1 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-283 : ℚ), (0 : ℚ), (-2971 : ℚ)], ![(1536 : ℚ), (2304 : ℚ), (-1536 : ℚ)], ![(-1435 : ℚ), (3072 : ℚ), (-1819 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

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

fc_compact_decl theorem excludes : Excludes 353 box (1) :=

  excludes_of_scaled_numerator 353 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf10

namespace Leaf11

fc_compact_decl def cert : Certificate := mkCert 353 ![![0, 24800, 0, 0], ![10826, 10826, 0, 0], ![0, 0, 19084, 0]] ![0, 75053, 61845]

fc_compact_decl def a : Seven := ![(-211435867217651007 / 167895496235417600 : ℚ), (0 : ℚ), (0 : ℚ), (75053 / 65536 : ℚ), (75053 / 65536 : ℚ), (61845 / 65536 : ℚ), (-4641652785 / 2501378048 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-139452107860614207 : ℚ), (-238552756097154400 : ℚ), (-840885141418847807 : ℚ)], ![(623106609825084000 : ℚ), (633758359660608000 : ℚ), (-623106609825084000 : ℚ)], ![(-456331287690918207 : ℚ), (1007660463553013600 : ℚ), (-524005961588543807 : ℚ)]]

fc_compact_decl def scale : ℚ := 167895496235417600

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

fc_compact_decl theorem excludes : Excludes 353 box (1) :=

  excludes_of_scaled_numerator 353 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf11

fc_compact_decl theorem node8 : Excludes 353 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 353 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) false (by convert Leaf10.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf10.box]) (by convert Leaf11.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf11.box])

namespace Leaf12

fc_compact_decl def cert : Certificate := mkCert 353 ![![0, 19456, 0, 0], ![13312, 13312, 0, 0], ![0, 0, 19456, 0]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(13 / 128 : ℚ), (0 : ℚ), (247 / 512 : ℚ), (19 / 32 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-247 : ℚ), (608 : ℚ), (-1349 : ℚ)], ![(494 : ℚ), (988 : ℚ), (494 : ℚ)], ![(-741 : ℚ), (608 : ℚ), (-855 : ℚ)]]

fc_compact_decl def scale : ℚ := 512

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

fc_compact_decl theorem excludes : Excludes 353 box (1) :=

  excludes_of_scaled_numerator 353 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf12

fc_compact_decl theorem node9 : Excludes 353 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 353 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert node8 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf12.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf12.box])

fc_compact_decl theorem node10 : Excludes 353 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 353 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert node7 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert node9 using 1 <;> norm_num [TBox.left, TBox.right])

fc_compact_decl theorem node11 : Excludes 353 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 353 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node4 node10

fc_compact_decl theorem excludes : Excludes 353 TBox.unit 0 := by
  simpa [TBox.unit] using node11

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case353


/- Generated compressed exclusion certificate. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSquares.CenterElimination.Compressed.Case354

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 354 ![![0, 0, 23723, 9541], ![1, 1, 1, 1], ![0, 32268, 0, 0]] ![49425, 34396, 49425]

fc_compact_decl def a : Seven := ![(12624229764439 / 23447967105024 : ℚ), (49425 / 65536 : ℚ), (22455425 / 103809024 : ℚ), (29142011 / 77856768 : ℚ), (8599 / 16384 : ℚ), (49425 / 65536 : ℚ), (-36833009225 / 976998629376 : ℚ)]

fc_compact_decl def n : Numerator := ![![(17840884472487 : ℚ), (22844939035728 : ℚ), (-35079700543609 : ℚ)], ![(11912267597400 : ℚ), (70734605356800 : ℚ), (8376298711800 : ℚ)], ![(-52893720884313 : ℚ), (26380907921328 : ℚ), (-35079700543609 : ℚ)]]

fc_compact_decl def scale : ℚ := 23447967105024

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, 1]

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

fc_compact_decl theorem excludes : Excludes 354 box (-1) :=

  excludes_of_scaled_numerator 354 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 354 ![![0, 0, 23723, 9541], ![1, 1, 1, 1], ![0, 32268, 0, 0]] ![98849, 68792, 98849]

fc_compact_decl def a : Seven := ![(-508736605465 / 710544457728 : ℚ), (98849 / 65536 : ℚ), (134731187 / 311427072 : ℚ), (29142011 / 38928384 : ℚ), (8599 / 8192 : ℚ), (98849 / 65536 : ℚ), (-4641863931011 / 1465497944064 : ℚ)]

fc_compact_decl def n : Numerator := ![![(32571574999783 : ℚ), (-99313798835296 : ℚ), (-73268879457241 : ℚ)], ![(168828006855560 : ℚ), (141467779563264 : ℚ), (-128251284729144 : ℚ)], ![(-108896204563481 : ℚ), (197765492749408 : ℚ), (-73268879457241 : ℚ)]]

fc_compact_decl def scale : ℚ := 23447967105024

fc_compact_decl def sigma : Fin 3 → ℚ := ![-1, -1, -1]

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

fc_compact_decl theorem excludes : Excludes 354 box (1) :=

  excludes_of_scaled_numerator 354 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

fc_compact_decl theorem node0 : Excludes 354 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 354 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) Leaf0.excludes Leaf1.excludes

fc_compact_decl theorem excludes : Excludes 354 TBox.unit 0 := by
  simpa [TBox.unit] using node0

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case354


/- Generated compressed exclusion certificate. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSquares.CenterElimination.Compressed.Case355

namespace Leaf0

fc_compact_decl def cert : Certificate := mkCert 355 ![![0, 0, 19456, 0], ![13312, 13312, 0, 0], ![0, 0, 0, 19456]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(13 / 128 : ℚ), (247 / 512 : ℚ), (0 : ℚ), (19 / 32 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (304 : ℚ), (-551 : ℚ)], ![(0 : ℚ), (494 : ℚ), (0 : ℚ)], ![(-494 : ℚ), (304 : ℚ), (-551 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

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

fc_compact_decl theorem excludes : Excludes 355 box (-1) :=

  excludes_of_scaled_numerator 355 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf0

namespace Leaf1

fc_compact_decl def cert : Certificate := mkCert 355 ![![0, 0, 24576, 0], ![12288, 12288, 0, 0], ![0, 0, 0, 16384]] ![0, 77824, 65536]

fc_compact_decl def a : Seven := ![(-1333 / 768 : ℚ), (0 : ℚ), (0 : ℚ), (19 / 16 : ℚ), (19 / 16 : ℚ), (1 : ℚ), (19 / 8 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-29 : ℚ), (171 : ℚ), (-134 : ℚ)], ![(-114 : ℚ), (96 : ℚ), (114 : ℚ)], ![(-77 : ℚ), (-57 : ℚ), (-86 : ℚ)]]

fc_compact_decl def scale : ℚ := 24

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

fc_compact_decl theorem excludes : Excludes 355 box (-1) :=

  excludes_of_scaled_numerator 355 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf1

namespace Leaf2

fc_compact_decl def cert : Certificate := mkCert 355 ![![0, 0, 24576, 0], ![8192, 8192, 0, 0], ![0, 0, 0, 24576]] ![0, 65536, 49152]

fc_compact_decl def a : Seven := ![(-11 / 24 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ), (1 : ℚ), (3 / 4 : ℚ), (1 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-283 : ℚ), (3072 : ℚ), (-2971 : ℚ)], ![(-1536 : ℚ), (2304 : ℚ), (1536 : ℚ)], ![(-1435 : ℚ), (0 : ℚ), (-1819 : ℚ)]]

fc_compact_decl def scale : ℚ := 768

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

fc_compact_decl theorem excludes : Excludes 355 box (-1) :=

  excludes_of_scaled_numerator 355 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf2

fc_compact_decl theorem node0 : Excludes 355 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 355 ⟨(0 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 : ℚ)⟩ (-1) false (by convert Leaf1.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf1.box]) (by convert Leaf2.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf2.box])

fc_compact_decl theorem node1 : Excludes 355 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 355 ⟨(0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) true (by convert Leaf0.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf0.box]) (by convert node0 using 1 <;> norm_num [TBox.left, TBox.right])

namespace Leaf3

fc_compact_decl def cert : Certificate := mkCert 355 ![![0, 0, 0, 19456], ![13312, 13312, 0, 0], ![0, 0, 0, 19456]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(13 / 128 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (0 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (0 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-152 : ℚ), (304 : ℚ), (-399 : ℚ)], ![(247 : ℚ), (494 : ℚ), (247 : ℚ)], ![(-646 : ℚ), (304 : ℚ), (-399 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

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

fc_compact_decl theorem excludes : Excludes 355 box (-1) :=

  excludes_of_scaled_numerator 355 box (-1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf3

fc_compact_decl theorem node2 : Excludes 355 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) :=
  excludes_split 355 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (-1) false (by convert node1 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf3.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf3.box])

namespace Leaf4

fc_compact_decl def cert : Certificate := mkCert 355 ![![0, 0, 19456, 0], ![13312, 13312, 0, 0], ![0, 0, 0, 19456]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(13 / 128 : ℚ), (247 / 512 : ℚ), (0 : ℚ), (19 / 32 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (-247 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(0 : ℚ), (57 : ℚ), (-551 : ℚ)], ![(247 : ℚ), (494 : ℚ), (-247 : ℚ)], ![(-494 : ℚ), (551 : ℚ), (-551 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

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

fc_compact_decl theorem excludes : Excludes 355 box (1) :=

  excludes_of_scaled_numerator 355 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf4

namespace Leaf5

fc_compact_decl def cert : Certificate := mkCert 355 ![![0, 0, 0, 18420], ![14656, 14656, 0, 0], ![0, 0, 0, 17804]] ![52624, 35589, 22679]

fc_compact_decl def a : Seven := ![(-23855320988678791 / 157497114954301440 : ℚ), (3289 / 4096 : ℚ), (3289 / 4096 : ℚ), (0 : ℚ), (35589 / 65536 : ℚ), (22679 / 65536 : ℚ), (-2779325089947 / 3582085038080 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-104355822386753671 : ℚ), (-73346675686342272 : ℚ), (-213360859924857991 : ℚ)], ![(497336330272029312 : ℚ), (218010075076208640 : ℚ), (8530868052870528 : ℚ)], ![(-466294459087307911 : ℚ), (415458786532816512 : ℚ), (-357289421549203591 : ℚ)]]

fc_compact_decl def scale : ℚ := 157497114954301440

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

fc_compact_decl theorem excludes : Excludes 355 box (1) :=

  excludes_of_scaled_numerator 355 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf5

namespace Leaf6

fc_compact_decl def cert : Certificate := mkCert 355 ![![0, 0, 0, 18432], ![13312, 13312, 0, 0], ![0, 10240, 0, 10240]] ![71680, 56320, 0]

fc_compact_decl def a : Seven := ![(-109507 / 119808 : ℚ), (35 / 32 : ℚ), (35 / 32 : ℚ), (0 : ℚ), (55 / 64 : ℚ), (0 : ℚ), (-1925 / 1152 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-177367 : ℚ), (-194480 : ℚ), (-177367 : ℚ)], ![(662480 : ℚ), (0 : ℚ), (-138320 : ℚ)], ![(-439447 : ℚ), (606320 : ℚ), (-439447 : ℚ)]]

fc_compact_decl def scale : ℚ := 119808

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

fc_compact_decl theorem excludes : Excludes 355 box (1) :=

  excludes_of_scaled_numerator 355 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf6

fc_compact_decl theorem node3 : Excludes 355 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) :=
  excludes_split 355 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 / 2 : ℚ)⟩ (1) false (by convert Leaf5.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf5.box]) (by convert Leaf6.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf6.box])

namespace Leaf7

fc_compact_decl def cert : Certificate := mkCert 355 ![![0, 0, 0, 19456], ![13312, 13312, 0, 0], ![0, 0, 0, 19456]] ![31616, 38912, 31616]

fc_compact_decl def a : Seven := ![(13 / 128 : ℚ), (247 / 512 : ℚ), (247 / 512 : ℚ), (0 : ℚ), (19 / 32 : ℚ), (247 / 512 : ℚ), (-247 / 512 : ℚ)]

fc_compact_decl def n : Numerator := ![![(-152 : ℚ), (57 : ℚ), (-399 : ℚ)], ![(494 : ℚ), (494 : ℚ), (0 : ℚ)], ![(-646 : ℚ), (551 : ℚ), (-399 : ℚ)]]

fc_compact_decl def scale : ℚ := 256

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

fc_compact_decl theorem excludes : Excludes 355 box (1) :=

  excludes_of_scaled_numerator 355 box (1) cert rfl a n sigma
    wellFormed signs coefficients scale (by norm_num [scale]) numerator_eq nonnegative

end Leaf7

fc_compact_decl theorem node4 : Excludes 355 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 355 ⟨(1 / 2 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) true (by convert node3 using 1 <;> norm_num [TBox.left, TBox.right]) (by convert Leaf7.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf7.box])

fc_compact_decl theorem node5 : Excludes 355 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) :=
  excludes_split 355 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (1) false (by convert Leaf4.excludes using 1 <;> norm_num [TBox.left, TBox.right, Leaf4.box]) (by convert node4 using 1 <;> norm_num [TBox.left, TBox.right])

fc_compact_decl theorem node6 : Excludes 355 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) :=
  excludes_diag 355 ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ), (1 : ℚ)⟩ (0) node2 node5

fc_compact_decl theorem excludes : Excludes 355 TBox.unit 0 := by
  simpa [TBox.unit] using node6

#print axioms excludes

end ThreeSquares.CenterElimination.Compressed.Case355
