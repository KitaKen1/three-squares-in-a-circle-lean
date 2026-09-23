import ThreeSquares.EdgeConstraints

/-! Necessary radial and pairwise-distance bounds for arbitrarily oriented
unit squares. Both signs of the orthogonal determinant are admitted. -/

open scoped NNReal

namespace ThreeSquares

/-- The coordinates in the inverse orthogonal frame preserve squared norm. -/
theorem OrthogonalCoefficients.projection_norm_sq (A : OrthogonalCoefficients) (x y : ℝ) :
    (x * A.a + y * A.c) ^ 2 + (x * A.b + y * A.d) ^ 2 = x ^ 2 + y ^ 2 := by
  have h0 := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f (point x y))
    (frameForm_coefficients_zero A)
  have h1 := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f (point x y))
    (frameForm_coefficients_one A)
  change A.toFrame.symm (point x y) 0 = A.a * x + A.c * y at h0
  change A.toFrame.symm (point x y) 1 = A.b * x + A.d * y at h1
  have hn := congrArg (fun z : ℝ => z ^ 2) (A.toFrame.symm.norm_map (point x y))
  rw [plane_norm_sq, plane_norm_sq, h0, h1] at hn
  simp only [point_zero, point_one] at hn
  nlinarith only [hn]

theorem OrthogonalCoefficients.projection_l1_ge_norm (A : OrthogonalCoefficients) (c : Plane) :
    ‖c‖ ≤ |c 0 * A.a + c 1 * A.c| + |c 0 * A.b + c 1 * A.d| := by
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mp
  rw [plane_norm_sq, ← A.projection_norm_sq (c 0) (c 1)]
  nlinarith only [sq_abs (c 0 * A.a + c 1 * A.c),
    sq_abs (c 0 * A.b + c 1 * A.d),
    mul_nonneg (abs_nonneg (c 0 * A.a + c 1 * A.c))
      (abs_nonneg (c 0 * A.b + c 1 * A.d))]

theorem center_radial_bound {r : ℝ≥0} {c : Plane} {A : OrthogonalCoefficients}
    (h : VertexInequalities r c A) : ‖c‖ ^ 2 + ‖c‖ + 1 / 2 ≤ (r : ℝ) ^ 2 := by
  have hv := vertex_bound_max ((inside_iff_four_vertex_bounds r c A).mp
    ((vertex_inequalities_iff_inside r c A).mp h))
  have hp := A.projection_l1_ge_norm c
  rw [← plane_norm_sq] at hv
  linarith only [hv, hp]

theorem radius_sq_ge_half {r : ℝ≥0} {c : Plane} {A : OrthogonalCoefficients}
    (h : VertexInequalities r c A) : (1 / 2 : ℝ) ≤ (r : ℝ) ^ 2 := by
  have hb := center_radial_bound h
  nlinarith only [hb, norm_nonneg c, sq_nonneg ‖c‖]

theorem center_norm_lt_eleven_sixteenths {r : ℝ≥0} {c : Plane}
    {A : OrthogonalCoefficients} (h : VertexInequalities r c A) (hr : r < radius) :
    ‖c‖ < 11 / 16 := by
  have hb := center_radial_bound h
  have hr' : (r : ℝ) < (radius : ℝ) := by exact_mod_cast hr
  have hs : (r : ℝ) ^ 2 < 425 / 256 := by
    nlinarith [radius_sq_real, r.coe_nonneg, radius.coe_nonneg]
  by_contra hn
  have hn' := le_of_not_gt hn
  nlinarith only [hb, hs, hn', sq_nonneg (‖c‖ - 11 / 16)]

theorem plane_coordinate_abs_le_norm (c : Plane) (k : Fin 2) : |c k| ≤ ‖c‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs, plane_norm_sq]
  fin_cases k
  · change c 0 ^ 2 ≤ c 0 ^ 2 + c 1 ^ 2
    exact le_add_of_nonneg_right (sq_nonneg _)
  · change c 1 ^ 2 ≤ c 0 ^ 2 + c 1 ^ 2
    exact le_add_of_nonneg_left (sq_nonneg _)

theorem center_coordinate_lt_eleven_sixteenths {r : ℝ≥0} {c : Plane}
    {A : OrthogonalCoefficients} (h : VertexInequalities r c A) (hr : r < radius)
    (k : Fin 2) : |c k| < 11 / 16 :=
  (plane_coordinate_abs_le_norm c k).trans_lt (center_norm_lt_eleven_sixteenths h hr)

theorem OrthogonalCoefficients.entries_bounded (A : OrthogonalCoefficients) :
    |A.a| ≤ 1 ∧ |A.b| ≤ 1 ∧ |A.c| ≤ 1 ∧ |A.d| ≤ 1 := by
  have h1 := A.first_unit
  have h2 := A.second_unit
  have ha := sq_nonneg A.a
  have hb := sq_nonneg A.b
  have hc := sq_nonneg A.c
  have hd := sq_nonneg A.d
  constructor
  · nlinarith [sq_abs A.a, abs_nonneg A.a]
  constructor
  · nlinarith [sq_abs A.b, abs_nonneg A.b]
  constructor
  · nlinarith [sq_abs A.c, abs_nonneg A.c]
  · nlinarith [sq_abs A.d, abs_nonneg A.d]

theorem OrthogonalCoefficients.projection_l1_ge_one (A : OrthogonalCoefficients)
    {u v : ℝ} (hn : u ^ 2 + v ^ 2 = 1) :
    1 ≤ |u * A.a + v * A.c| + |u * A.b + v * A.d| := by
  apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
    (add_nonneg (abs_nonneg _) (abs_nonneg _))).mp
  have hp := A.projection_norm_sq u v
  nlinarith only [hp, hn, sq_abs (u * A.a + v * A.c), sq_abs (u * A.b + v * A.d),
    mul_nonneg (abs_nonneg (u * A.a + v * A.c)) (abs_nonneg (u * A.b + v * A.d))]

theorem axis_implies_center_distance_sq {c d : Plane} {A B : OrthogonalCoefficients}
    {u v : ℝ} (h : AxisInequality c d A B u v) (hn : u ^ 2 + v ^ 2 = 1) :
    1 ≤ (d 0 - c 0) ^ 2 + (d 1 - c 1) ^ 2 := by
  have ha := A.projection_l1_ge_one hn
  have hb := B.projection_l1_ge_one hn
  have hdot : 1 ≤ |u * (d 0 - c 0) + v * (d 1 - c 1)| := by
    unfold AxisInequality at h
    linarith only [h, ha, hb]
  have hs : 1 ≤ (u * (d 0 - c 0) + v * (d 1 - c 1)) ^ 2 := by
    have := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg _)).mpr hdot
    simpa only [one_pow, sq_abs] using this
  have hid : (u * (d 0 - c 0) + v * (d 1 - c 1)) ^ 2 +
      (v * (d 0 - c 0) - u * (d 1 - c 1)) ^ 2 =
      (u ^ 2 + v ^ 2) * ((d 0 - c 0) ^ 2 + (d 1 - c 1) ^ 2) := by ring
  rw [hn, one_mul] at hid
  nlinarith only [hs, hid, sq_nonneg (v * (d 0 - c 0) - u * (d 1 - c 1))]

theorem separated_centers_distance_sq {c d : Plane} {A B : OrthogonalCoefficients}
    (h : FourAxisSeparation c d A B) :
    1 ≤ (d 0 - c 0) ^ 2 + (d 1 - c 1) ^ 2 := by
  rcases h with h | h | h | h
  · exact axis_implies_center_distance_sq h A.first_unit
  · exact axis_implies_center_distance_sq h A.second_unit
  · exact axis_implies_center_distance_sq h B.first_unit
  · exact axis_implies_center_distance_sq h B.second_unit

end ThreeSquares
