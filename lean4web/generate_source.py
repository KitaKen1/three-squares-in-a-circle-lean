#!/usr/bin/env python3
"""Generate the single-file Lean4Web edition from the FC-target project."""

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1] / "lean"
OUT = Path(__file__).resolve().parent / "ThreeSquaresLean4Web.lean"
FC_COMMIT = "8927a585c5d522fc132d7ea6488fcd9e30ccd80e"


def module_path(name: str) -> Path:
    return ROOT.joinpath(*name.split(".")).with_suffix(".lean")


def imports(path: Path) -> list[str]:
    return re.findall(r"^import\s+([A-Za-z0-9_.]+)\s*$", path.read_text(), re.M)


def rename_private_declarations(source: str, module: str) -> str:
    """Preserve file-local privacy when formerly separate modules are joined."""
    # Lean 4 Web's style linter warns about names beginning with underscores.
    # A stable, ordinary prefix still keeps formerly file-local names unique.
    prefix = "fw" + module.replace(".", "_")
    declaration = re.compile(
        r"(?m)^private\s+(?:(?:noncomputable|unsafe)\s+)*"
        r"(?:theorem|lemma|def|abbrev|opaque|inductive|structure)\s+"
        r"([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)"
    )
    names = [match.group(1) for match in declaration.finditer(source)]
    for name in names:
        if "." in name:
            namespace, short = name.rsplit(".", 1)
            replacement = f"{namespace}.{prefix}_{short}"
        else:
            replacement = f"{prefix}_{name}"
        source = re.sub(
            rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])",
            replacement,
            source,
        )
    return source


def update_lean435_names(source: str) -> str:
    """Use the replacement names from Lean 4.35's deprecation messages.

    Keep this compatibility adaptation in the browser generator: the pinned
    FC project still uses Lean 4.33.1, and its proof sources are unchanged.
    """
    replacements = {
        "if_pos": "ite_eq_left", "if_neg": "ite_eq_right",
        "if_true": "ite_true", "if_false": "ite_false",
    }
    return re.sub(r"(?<![A-Za-z0-9_'])\b(?:if_pos|if_neg|if_true|if_false)\b(?![A-Za-z0-9_'])",
                  lambda match: replacements[match.group()], source)


def add_tail_diagnostics(source: str) -> str:
    """Locate a failure after the last certificate, without changing proofs."""
    phases = {
        "repTrees_codes": "tail 1/4: checking the representative-code list",
        "repTrees_check": "tail 2/4: assembling the 64 certificate proofs",
        "word_mem": "tail 4/4: connecting the correspondence table to the lower bound",
    }
    for theorem, message in phases.items():
        needle = f"\ntheorem {theorem} "
        assert source.count(needle) == 1, theorem
        source = source.replace(needle, f'\n#print "ThreeSquares: {message}."\n{needle}')
    needle = "\nprivate theorem word_block_0 "
    assert source.count(needle) == 1
    source = source.replace(needle,
        '\n#print "ThreeSquares: tail 3/4: checking 512 branches in 16 blocks of 32."\n' + needle)
    return source


def split_word_verification(source: str) -> str:
    """Preserve the 512-case theorem, but bound each kernel computation to 32 cases.

    Do not change the correspondence table or its lookup. The final proof uses
    quotient/remainder to cover every c < 512, including the last case, 511.
    This adaptation is only for the single-file edition; the pinned FC source
    and its verification record remain unchanged.
    """
    original = '''theorem word_reaches_rep :
    ((List.range 512).all fun c => repCodes.contains (applyCode (word c).1 (word c).2 c)) = true := by
  decide +kernel'''
    assert source.count(original) == 1
    blocks = []
    for i in range(16):
        c = f"({i} * 32 + j)"
        blocks.append(f'''private theorem word_block_{i} :
    ((List.range 32).all fun j =>
      repCodes.contains (applyCode (word {c}).1 (word {c}).2 {c})) = true := by
  decide +kernel
''')
    blocks.append('''private theorem word_blocks (i : Fin 16) :
    ((List.range 32).all fun j =>
      repCodes.contains (applyCode (word (i.val * 32 + j)).1
        (word (i.val * 32 + j)).2 (i.val * 32 + j))) = true := by
  fin_cases i
''' + "".join(f"  · exact word_block_{i}\n" for i in range(16)))
    blocks.append('''theorem word_reaches_rep :
    ((List.range 512).all fun c => repCodes.contains (applyCode (word c).1 (word c).2 c)) = true := by
  rw [List.all_eq_true]
  intro c hc
  have hlt : c < 512 := List.mem_range.mp hc
  have hq : c / 32 < 16 := by omega
  have h := word_blocks ⟨c / 32, hq⟩
  rw [List.all_eq_true] at h
  have hr : c % 32 ∈ List.range 32 := List.mem_range.mpr (Nat.mod_lt _ (by decide))
  have heq : c / 32 * 32 + c % 32 = c := by omega
  simpa only [heq] using h (c % 32) hr
''')
    return source.replace(original, "\n".join(blocks).rstrip())


visited: set[str] = set()
ordered: list[tuple[str, Path]] = []


def visit(name: str) -> None:
    if name in visited:
        return
    visited.add(name)
    path = module_path(name)
    if not path.is_file():
        raise SystemExit(f"Missing source for imported module {name}: {path}")
    for dependency in imports(path):
        if dependency.startswith("ThreeSquares"):
            visit(dependency)
        elif dependency.startswith("FormalConjectures"):
            # The web file embeds the exact four target definitions below.
            continue
        else:
            # The browser edition uses Mathlib's umbrella import.
            continue
    # ThreeSquares.lean is only the Lake aggregator; its imports were visited.
    if name != "ThreeSquares":
        ordered.append((name, path))


for root_module in [
    "ThreeSquares.UpperBound",
    "ThreeSquares.Target",
    "ThreeSquares.RepTrees",
]:
    visit(root_module)

header = f'''import Mathlib

/-!
Generated by `lean4web/generate_source.py` from the FC-compatible sources.

The four declarations in `SquarePacking` below are copied verbatim in meaning
from Formal Conjectures `Wikipedia/SquarePacking.lean` at commit `{FC_COMMIT}`.
The main Lake project imports that module directly; these definitions are
embedded only so this single file can be pasted into Lean4Web.

This file is intentionally a full proof artifact, not just a statement check.
-/
set_option autoImplicit false
-- The language server otherwise elaborates theorem bodies asynchronously.
-- Keep the large certificate checks sequential to limit concurrent work.
set_option Elab.async false

open EuclideanGeometry
open scoped NNReal

-- The Formal Conjectures target scopes this notation through its geometry
-- utility module. Re-declare its exact meaning for the single-file edition.
scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
open scoped EuclideanGeometry

namespace SquarePacking

/-- The open axis-aligned square of side length `side`. -/
def Square (side : ℝ) : Set ℝ² :=
  {{p : ℝ² | 0 < p 0 ∧ p 0 < side ∧ 0 < p 1 ∧ p 1 < side}}

/-- The open unit square, exactly as in the pinned FC target. -/
def UnitSquare : Set ℝ² := Square 1

/-- The open disc of nonnegative radius `r`, exactly as in the pinned FC target. -/
def Circle (r : ℝ≥0) : Set ℝ² :=
  {{p : ℝ² | p 0 ^ 2 + p 1 ^ 2 < (r : ℝ) ^ 2}}

/-- Isometric copies of a shape, pairwise disjoint and inside a container. -/
structure Packing (n : ℕ) (s : Set ℝ²) (S : Set ℝ²) where
  embeddings : Fin n → (ℝ² ≃ᵢ ℝ²)
  disjoint : Pairwise fun i j => Disjoint (embeddings i '' s) (embeddings j '' s)
  inside : ∀ i : Fin n, embeddings i '' s ⊆ S

end SquarePacking

'''

chunks = [header]
for name, path in ordered:
    source = path.read_text()
    source = re.sub(r"^import\s+[^\n]*(?:\n|$)", "", source, flags=re.M)
    if name == "ThreeSquares.RepTrees":
        source = split_word_verification(source)
        source = add_tail_diagnostics(source)
    source = rename_private_declarations(source, name)
    source = update_lean435_names(source)
    if name == "ThreeSquares.RepTrees.Part00":
        chunks.append('#print "ThreeSquares: starting certificate groups (0/16)."\n')
    chunks.append(f"\n/-! Lean4Web source module: `{name}`. -/\n\n{source.rstrip()}\n")
    if match := re.fullmatch(r"ThreeSquares\.RepTrees\.Part(\d{2})", name):
        group = int(match.group(1)) + 1
        chunks.append(
            f'#print "ThreeSquares: reached end of certificate group {group}/16; '
            'final axiom audit still required."\n'
        )

chunks.append('''
#print "ThreeSquares: reached final declarations; beginning lower-bound axiom audit."
#check ThreeSquares.global_lower_bound
#print axioms ThreeSquares.global_lower_bound
#print "ThreeSquares: beginning final IsLeast axiom audit."
#check ThreeSquares.least_three_square_packing_in_circle
#print axioms ThreeSquares.least_three_square_packing_in_circle
''')
OUT.write_text("\n".join(chunks))
print(f"Wrote {OUT} from {len(ordered)} local Lean modules")
