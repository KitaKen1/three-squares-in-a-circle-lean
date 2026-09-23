import ThreeSquares.Compressed.Main

/-! Provenance, target-type, and axiom checks for the compressed FC proof. -/

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
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`ThreeSquares.CenterElimination.Compressed.global_lower_bound,
      `ThreeSquares.CenterElimination.Compressed.least_three_square_packing_in_circle] do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom in {name}: {axiomName}"
    logInfo m!"Axiom check passed: {name}: {axioms}"
  for name in #[`SquarePacking.three_square_packing_in_circle_bound,
      `SquarePacking.least_three_square_packing_in_circle] do
    unless (← collectAxioms name).contains `sorryAx do
      throwError "Pinned upstream negative control changed: {name}"
    logInfo m!"Upstream negative control contains sorryAx: {name}"

run_cmd do
  liftTermElabM do
    let fc := (← getConstInfo `SquarePacking.least_three_square_packing_in_circle).type
    let ours := (← getConstInfo
      `ThreeSquares.CenterElimination.Compressed.least_three_square_packing_in_circle).type
    match fc.getAppFnArgs, ours.getAppFnArgs with
    | (``IsLeast, #[_, _, s1, _]), (``IsLeast, #[_, _, s2, v]) =>
      unless ← Meta.isDefEq s1 s2 do
        throwError "The feasible-radius set differs from FC"
      logInfo m!"Compressed result proves the actual FC IsLeast set with answer {v}"
    | _, _ => throwError "Unexpected IsLeast statement shape"

open scoped NNReal in
example : IsLeast {r : ℝ≥0 | Nonempty
    (SquarePacking.Packing 3 SquarePacking.UnitSquare (SquarePacking.Circle r))}
    ((5 * NNReal.sqrt 17) / 16) :=
  ThreeSquares.CenterElimination.Compressed.least_three_square_packing_in_circle
