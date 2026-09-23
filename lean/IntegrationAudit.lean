import ThreeSquares

/-! # Checks for the connection to the actual Formal Conjectures module

These checks inspect declaration provenance and compare the upper-bound types.
The upstream conjectures are negative controls, never premises of our proofs.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for name in #[`SquarePacking.Square, `SquarePacking.UnitSquare,
      `SquarePacking.Circle, `SquarePacking.Packing] do
    let some idx := env.getModuleIdxFor? name
      | throwError "Not imported: {name}"
    let source := env.header.moduleNames[idx.toNat]!
    unless source == `FormalConjectures.Wikipedia.SquarePacking do
      throwError "Wrong definition source for {name}: {source}"
    logInfo m!"Upstream definition: {name} from {source}"

run_cmd do
  liftTermElabM do
    let expected := (← getConstInfo `SquarePacking.three_square_packing_in_circle_bound).type
    let actual := (← getConstInfo `ThreeSquares.three_square_packing_in_circle_bound).type
    unless ← Meta.isDefEq actual expected do
      throwError "The upper-bound statement differs from FC"
    logInfo "Upper-bound type matches the actual FC declaration"

run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`ThreeSquares.three_square_packing_in_circle_bound,
      `ThreeSquares.least_axis_aligned_radius,
      `ThreeSquares.local_algebra_rigidity,
      `ThreeSquares.local_algebra_rigidity_four,
      `ThreeSquares.local_constraints_of_geometry,
      `ThreeSquares.local_geometry_rigidity,
      `ThreeSquares.local_geometry_radius_lower_bound,
      `ThreeSquares.placedSquare_orient,
      `ThreeSquares.normalized_oriented_edge_constraints_packing_iff,
      `ThreeSquares.placedSquare_quadrant,
      `ThreeSquares.first_quadrant_rational_parameters,
      `ThreeSquares.normalized_rational_rotation_packing_iff,
      `ThreeSquares.smaller_fc_packing_has_eight_variable_witness,
      `ThreeSquares.RationalPackingFormula.smaller_fc_packing_has_eight_variable_assignment,
      `ThreeSquares.RationalPackingFormula.global_lower_bound_of_empty_eight_variable_certificate,
      `ThreeSquares.RationalPackingFormula.quadrant_assignment_two_orbits,
      `ThreeSquares.RationalPackingFormula.smaller_fc_packing_in_one_of_24_quadrant_boxes,
      `ThreeSquares.normalized_coefficient_packing_iff,
      `ThreeSquares.rotated_four_vertex_bounds,
      `ThreeSquares.coefficient_disjoint_iff_separator,
      `ThreeSquares.inside_iff_four_vertex_bounds,
      `ThreeSquares.normalized_finite_constraints_packing_iff,
      `ThreeSquares.global_lower_bound_iff_no_smaller_finite_constraints,
      `ThreeSquares.disjoint_iff_four_axes,
      `ThreeSquares.normalized_edge_constraints_packing_iff,
      `ThreeSquares.global_lower_bound_iff_no_smaller_edge_constraints,
      `ThreeSquares.global_lower_bound_iff_no_smaller_normalized,
      `ThreeSquares.IntervalCertificate.check_sound,
      `ThreeSquares.IntervalCertificate.exclude_sound,
      `ThreeSquares.PackingFormula.formula_holds,
      `ThreeSquares.PackingFormula.smaller_fc_packing_has_assignment,
      `ThreeSquares.PackingFormula.global_lower_bound_of_empty_certificate,
      `ThreeSquares.PackingCertificateExamples.overlap_box_infeasible,
      `ThreeSquares.IntervalCertificate.search_accepted,
      `ThreeSquares.GeneratedCertificates.RotatedOverlap6.infeasible,
      `ThreeSquares.PackingFormula.generated_initial_localizes_smaller_fc_packing,
      `ThreeSquares.center_radial_bound,
      `ThreeSquares.center_norm_lt_eleven_sixteenths,
      `ThreeSquares.separated_centers_distance_sq,
      `ThreeSquares.PackingFormula.smaller_fc_packing_has_contracted_assignment,
      `ThreeSquares.PackingFormula.focused6_localizes_smaller_fc_packing,
      `ThreeSquares.PackingFormula.focused8_localizes_smaller_fc_packing,
      `ThreeSquares.RationalPackingFormula.smaller_fc_packing_in_representative_box,
      `ThreeSquares.RationalPackingFormula.global_lower_bound_of_two_representative_certificates,
      `ThreeSquares.least_three_square_packing_in_circle_of_lower_bound,
      `ThreeSquares.global_lower_bound,
      `ThreeSquares.least_three_square_packing_in_circle] do
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom in {name}: {axiomName}"
    logInfo m!"Axiom check passed: {name}"
  for name in #[`SquarePacking.three_square_packing_in_circle_bound,
      `SquarePacking.least_three_square_packing_in_circle] do
    unless (← collectAxioms name).contains `sorryAx do
      throwError "The pinned upstream negative control changed: {name}"
    logInfo m!"Negative control contains sorryAx as expected: {name}"

run_cmd do
  liftTermElabM do
    let fc := (← getConstInfo `SquarePacking.least_three_square_packing_in_circle).type
    let ours := (← getConstInfo `ThreeSquares.least_three_square_packing_in_circle).type
    match fc.getAppFnArgs, ours.getAppFnArgs with
    | (``IsLeast, #[_, _, s1, _]), (``IsLeast, #[_, _, s2, v]) =>
      unless ← Meta.isDefEq s1 s2 do
        throwError "The feasible-radius set differs from the FC statement"
      logInfo m!"Final theorem proves IsLeast of the FC set with answer {v}"
    | _, _ => throwError "Unexpected shape of the IsLeast statements"
