import ThreeSquares.Compressed.Part00
import ThreeSquares.Compressed.Part01
import ThreeSquares.Compressed.Part02
import ThreeSquares.Compressed.Part03
import ThreeSquares.Compressed.Part04
import ThreeSquares.Compressed.Part05
import ThreeSquares.Compressed.Part06
import ThreeSquares.Compressed.Part07
import ThreeSquares.Compressed.Part08
import ThreeSquares.Compressed.Part09
import ThreeSquares.Compressed.Part10
import ThreeSquares.Compressed.Part11
import ThreeSquares.Compressed.Part12
import ThreeSquares.Compressed.Part13
import ThreeSquares.Compressed.Part14
import ThreeSquares.Compressed.Part15

/-! The compressed proof of the pinned Formal Conjectures target. -/
set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace ThreeSquares.CenterElimination.Compressed
open scoped NNReal
open SquarePacking

fc_compact_decl def repCodes : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 32, 33, 34, 35, 40, 41, 42, 43, 64, 65, 66, 67, 72, 73, 74, 75, 80, 81, 82, 83, 88, 89, 90, 91, 96, 97, 98, 99, 104, 105, 106, 107, 112, 113, 114, 115, 120, 121, 122, 123, 320, 321, 322, 323, 328, 329, 330, 331, 352, 353, 354, 355, 360, 361, 362, 363]

fc_compact_decl def wordTable : List (ℕ × Bool) := [(0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (0, false), (0, false), (0, false), (0, false), (2, false), (2, false), (2, false), (2, false), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true), (2, true), (2, true), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, false), (3, false), (3, false), (3, false), (1, false), (1, false), (1, false), (1, false), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true), (3, true), (3, true), (1, true), (1, true)]

fc_compact_decl def word (c : ℕ) : ℕ × Bool := wordTable.getD c (0, false)

fc_compact_decl theorem word_block_0 :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (0 * 32 + j)).1 (word (0 * 32 + j)).2 (0 * 32 + j))) = true := by
  decide +kernel

fc_compact_decl theorem word_block_1 :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (1 * 32 + j)).1 (word (1 * 32 + j)).2 (1 * 32 + j))) = true := by
  decide +kernel

fc_compact_decl theorem word_block_2 :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (2 * 32 + j)).1 (word (2 * 32 + j)).2 (2 * 32 + j))) = true := by
  decide +kernel

fc_compact_decl theorem word_block_3 :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (3 * 32 + j)).1 (word (3 * 32 + j)).2 (3 * 32 + j))) = true := by
  decide +kernel

fc_compact_decl theorem word_block_4 :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (4 * 32 + j)).1 (word (4 * 32 + j)).2 (4 * 32 + j))) = true := by
  decide +kernel

fc_compact_decl theorem word_block_5 :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (5 * 32 + j)).1 (word (5 * 32 + j)).2 (5 * 32 + j))) = true := by
  decide +kernel

fc_compact_decl theorem word_block_6 :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (6 * 32 + j)).1 (word (6 * 32 + j)).2 (6 * 32 + j))) = true := by
  decide +kernel

fc_compact_decl theorem word_block_7 :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (7 * 32 + j)).1 (word (7 * 32 + j)).2 (7 * 32 + j))) = true := by
  decide +kernel

fc_compact_decl theorem word_block_8 :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (8 * 32 + j)).1 (word (8 * 32 + j)).2 (8 * 32 + j))) = true := by
  decide +kernel

fc_compact_decl theorem word_block_9 :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (9 * 32 + j)).1 (word (9 * 32 + j)).2 (9 * 32 + j))) = true := by
  decide +kernel

fc_compact_decl theorem word_block_10 :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (10 * 32 + j)).1 (word (10 * 32 + j)).2 (10 * 32 + j))) = true := by
  decide +kernel

fc_compact_decl theorem word_block_11 :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (11 * 32 + j)).1 (word (11 * 32 + j)).2 (11 * 32 + j))) = true := by
  decide +kernel

fc_compact_decl theorem word_block_12 :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (12 * 32 + j)).1 (word (12 * 32 + j)).2 (12 * 32 + j))) = true := by
  decide +kernel

fc_compact_decl theorem word_block_13 :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (13 * 32 + j)).1 (word (13 * 32 + j)).2 (13 * 32 + j))) = true := by
  decide +kernel

fc_compact_decl theorem word_block_14 :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (14 * 32 + j)).1 (word (14 * 32 + j)).2 (14 * 32 + j))) = true := by
  decide +kernel

fc_compact_decl theorem word_block_15 :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (15 * 32 + j)).1 (word (15 * 32 + j)).2 (15 * 32 + j))) = true := by
  decide +kernel

fc_compact_decl theorem word_blocks (i : Fin 16) :
    ((List.range 32).all fun j => repCodes.contains
      (applyCode (word (i.val * 32 + j)).1 (word (i.val * 32 + j)).2 (i.val * 32 + j))) = true := by
  fin_cases i
  · exact word_block_0
  · exact word_block_1
  · exact word_block_2
  · exact word_block_3
  · exact word_block_4
  · exact word_block_5
  · exact word_block_6
  · exact word_block_7
  · exact word_block_8
  · exact word_block_9
  · exact word_block_10
  · exact word_block_11
  · exact word_block_12
  · exact word_block_13
  · exact word_block_14
  · exact word_block_15

fc_compact_decl theorem word_mem (c : ℕ) (hc : c < 512) :
    applyCode (word c).1 (word c).2 c ∈ repCodes := by
  have hq : c / 32 < 16 := by omega
  have h := word_blocks ⟨c / 32, hq⟩
  rw [List.all_eq_true] at h
  have hm : c % 32 ∈ List.range 32 := List.mem_range.mpr (Nat.mod_lt _ (by decide))
  have heq : c / 32 * 32 + c % 32 = c := by omega
  have hh := h (c % 32) hm
  simpa only [heq, List.contains_iff_mem] using hh

fc_compact_decl theorem representatives_excluded : ∀ c ∈ repCodes, Excludes c TBox.unit 0 := by
  intro c hc
  simp only [repCodes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Case000.excludes
  · exact Case001.excludes
  · exact Case002.excludes
  · exact Case003.excludes
  · exact Case008.excludes
  · exact Case009.excludes
  · exact Case010.excludes
  · exact Case011.excludes
  · exact Case032.excludes
  · exact Case033.excludes
  · exact Case034.excludes
  · exact Case035.excludes
  · exact Case040.excludes
  · exact Case041.excludes
  · exact Case042.excludes
  · exact Case043.excludes
  · exact Case064.excludes
  · exact Case065.excludes
  · exact Case066.excludes
  · exact Case067.excludes
  · exact Case072.excludes
  · exact Case073.excludes
  · exact Case074.excludes
  · exact Case075.excludes
  · exact Case080.excludes
  · exact Case081.excludes
  · exact Case082.excludes
  · exact Case083.excludes
  · exact Case088.excludes
  · exact Case089.excludes
  · exact Case090.excludes
  · exact Case091.excludes
  · exact Case096.excludes
  · exact Case097.excludes
  · exact Case098.excludes
  · exact Case099.excludes
  · exact Case104.excludes
  · exact Case105.excludes
  · exact Case106.excludes
  · exact Case107.excludes
  · exact Case112.excludes
  · exact Case113.excludes
  · exact Case114.excludes
  · exact Case115.excludes
  · exact Case120.excludes
  · exact Case121.excludes
  · exact Case122.excludes
  · exact Case123.excludes
  · exact Case320.excludes
  · exact Case321.excludes
  · exact Case322.excludes
  · exact Case323.excludes
  · exact Case328.excludes
  · exact Case329.excludes
  · exact Case330.excludes
  · exact Case331.excludes
  · exact Case352.excludes
  · exact Case353.excludes
  · exact Case354.excludes
  · exact Case355.excludes
  · exact Case360.excludes
  · exact Case361.excludes
  · exact Case362.excludes
  · exact Case363.excludes

fc_compact_decl theorem global_lower_bound : GlobalLowerBound :=
  global_lower_bound_of_excludes repCodes word word_mem representatives_excluded

fc_compact_decl theorem least_three_square_packing_in_circle :
    IsLeast {r : ℝ≥0 | Nonempty (Packing 3 UnitSquare (Circle r))}
      ((5 * NNReal.sqrt 17) / 16) :=
  least_three_square_packing_in_circle_of_lower_bound global_lower_bound

#check least_three_square_packing_in_circle
#print axioms global_lower_bound
#print axioms least_three_square_packing_in_circle

end ThreeSquares.CenterElimination.Compressed
