import ThreeSquares.BranchSymmetry
import ThreeSquares.RepTrees.Part00
import ThreeSquares.RepTrees.Part01
import ThreeSquares.RepTrees.Part02
import ThreeSquares.RepTrees.Part03
import ThreeSquares.RepTrees.Part04
import ThreeSquares.RepTrees.Part05
import ThreeSquares.RepTrees.Part06
import ThreeSquares.RepTrees.Part07
import ThreeSquares.RepTrees.Part08
import ThreeSquares.RepTrees.Part09
import ThreeSquares.RepTrees.Part10
import ThreeSquares.RepTrees.Part11
import ThreeSquares.RepTrees.Part12
import ThreeSquares.RepTrees.Part13
import ThreeSquares.RepTrees.Part14
import ThreeSquares.RepTrees.Part15

/-! # The unconditional lower bound and the FC answer

The 64 representative certificate trees are checked by the kernel in the
generated files.  Every one of the 512 separation branches is moved to a
representative by the symmetry word table below. -/

namespace ThreeSquares.CenterElimination

open scoped NNReal
open SquarePacking

def repTrees : List CodedGTree :=
  RepTrees.Part00.trees ++
    RepTrees.Part01.trees ++
    RepTrees.Part02.trees ++
    RepTrees.Part03.trees ++
    RepTrees.Part04.trees ++
    RepTrees.Part05.trees ++
    RepTrees.Part06.trees ++
    RepTrees.Part07.trees ++
    RepTrees.Part08.trees ++
    RepTrees.Part09.trees ++
    RepTrees.Part10.trees ++
    RepTrees.Part11.trees ++
    RepTrees.Part12.trees ++
    RepTrees.Part13.trees ++
    RepTrees.Part14.trees ++
    RepTrees.Part15.trees

def repCodes : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 32, 33, 34, 35, 40, 41, 42, 43, 64, 65, 66, 67, 72, 73, 74, 75, 80, 81, 82, 83, 88, 89, 90, 91, 96, 97, 98, 99, 104, 105, 106, 107, 112, 113, 114, 115, 120, 121, 122, 123, 320, 321, 322, 323, 328, 329, 330, 331, 352, 353, 354, 355, 360, 361, 362, 363]

theorem repTrees_codes : repTrees.map CodedGTree.code = repCodes := by
  decide +kernel

private theorem check_append {left right : List CodedGTree}
    (hleft : ∀ T ∈ left, T.tree.check T.code TBox.unit 0 = true)
    (hright : ∀ T ∈ right, T.tree.check T.code TBox.unit 0 = true) :
    ∀ T ∈ left ++ right, T.tree.check T.code TBox.unit 0 = true := by
  intro T hT
  rcases List.mem_append.mp hT with h | h
  · exact hleft T h
  · exact hright T h

theorem repTrees_check : ∀ T ∈ repTrees, T.tree.check T.code TBox.unit 0 = true := by
  simp only [repTrees, List.append_assoc]
  apply check_append
  · exact RepTrees.Part00.trees_check
  · apply check_append
    · exact RepTrees.Part01.trees_check
    · apply check_append
      · exact RepTrees.Part02.trees_check
      · apply check_append
        · exact RepTrees.Part03.trees_check
        · apply check_append
          · exact RepTrees.Part04.trees_check
          · apply check_append
            · exact RepTrees.Part05.trees_check
            · apply check_append
              · exact RepTrees.Part06.trees_check
              · apply check_append
                · exact RepTrees.Part07.trees_check
                · apply check_append
                  · exact RepTrees.Part08.trees_check
                  · apply check_append
                    · exact RepTrees.Part09.trees_check
                    · apply check_append
                      · exact RepTrees.Part10.trees_check
                      · apply check_append
                        · exact RepTrees.Part11.trees_check
                        · apply check_append
                          · exact RepTrees.Part12.trees_check
                          · apply check_append
                            · exact RepTrees.Part13.trees_check
                            · apply check_append
                              · exact RepTrees.Part14.trees_check
                              · exact RepTrees.Part15.trees_check

def wordTable : List (ℕ × Bool) := [(0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true)]

def word (c : ℕ) : ℕ × Bool := wordTable.getD c (0, false)

theorem word_reaches_rep :
    ((List.range 512).all fun c => repCodes.contains (applyCode (word c).1 (word c).2 c)) = true := by
  decide +kernel

theorem word_mem (c : ℕ) (hc : c < 512) :
    applyCode (word c).1 (word c).2 c ∈ repTrees.map CodedGTree.code := by
  rw [repTrees_codes]
  have h := word_reaches_rep
  simp only [List.all_eq_true, List.mem_range, List.contains_iff_mem] at h
  simpa using h c hc

end ThreeSquares.CenterElimination

namespace ThreeSquares

open scoped NNReal
open SquarePacking

/-- The unconditional lower bound: no three unit squares fit in a circle of
radius smaller than `5√17/16`. -/
theorem global_lower_bound : GlobalLowerBound :=
  CenterElimination.global_lower_bound_of_rep_trees CenterElimination.repTrees
    CenterElimination.word CenterElimination.word_mem CenterElimination.repTrees_check

/-- The Formal Conjectures statement with the exact answer `5√17/16`. -/
theorem least_three_square_packing_in_circle :
    IsLeast {r : ℝ≥0 | Nonempty (Packing 3 UnitSquare (Circle r))} ((5 * NNReal.sqrt 17) / 16) :=
  least_three_square_packing_in_circle_of_lower_bound global_lower_bound

end ThreeSquares
