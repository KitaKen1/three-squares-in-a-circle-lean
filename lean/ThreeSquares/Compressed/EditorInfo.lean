import Lean

/-! Generated certificate declarations can omit intermediate editor metadata.
This wrapper calls the ordinary command elaborator with info-tree recording
disabled. It does not catch errors, change proofs, add axioms, or disable the
kernel. Remove `fc_compact_decl` from a declaration to inspect its tactic goals.
The unused/unreachable tactic linters require that metadata, so generated
modules disable those two linters locally. -/

open Lean Elab Command in
elab "fc_compact_decl" cmd:command : command =>
  withEnableInfoTree false (elabCommand cmd)
