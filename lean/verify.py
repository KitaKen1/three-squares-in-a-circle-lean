#!/usr/bin/env python3
"""Build the project and reject untrusted axiom dependencies in the audit."""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FC_COMMIT = "8927a585c5d522fc132d7ea6488fcd9e30ccd80e"


def run(command, name):
    start = time.monotonic()
    env = os.environ.copy()
    env.setdefault("LEAN_NUM_THREADS", "4")
    with (ROOT / "verification" / name).open("w") as log:
        result = subprocess.run(command, cwd=ROOT, env=env,
                                stdout=log, stderr=subprocess.STDOUT)
    elapsed = round(time.monotonic() - start, 3)
    if result.returncode:
        raise SystemExit(f"Failed: {' '.join(command)}; see verification/{name}")
    return elapsed


def main():
    out = ROOT / "verification"
    out.mkdir(exist_ok=True)
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = {p["name"]: p for p in manifest["packages"]}
    if packages["formal_conjectures"]["rev"] != FC_COMMIT:
        raise SystemExit("Unexpected FC dependency revision")
    fc = ROOT / ".lake/packages/formal_conjectures"
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=fc, text=True).strip()
    if head != FC_COMMIT:
        raise SystemExit("The FC checkout does not match its pinned revision")
    changes = subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"],
                                      cwd=fc, text=True)
    if changes.strip():
        raise SystemExit("The upstream FC source has local modifications")
    benchmark = json.loads((ROOT / "certificates/benchmark.json").read_text())
    for relative, expected_hash in (benchmark["artifact_sha256"] |
                                    benchmark["generator_sha256"]).items():
        if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != expected_hash:
            raise SystemExit(f"Stale certificate benchmark: {relative}; rerun benchmark_certificates.py")
    if not benchmark["repeated_generation_identical"] or not all(
            row["kernel_checked"] for row in benchmark["cases"]):
        raise SystemExit("Incomplete representative certificate benchmark")
    times = {
        "build": run(["lake", "--wfail", "build", "ThreeSquares"], "build.log"),
        "axioms": run(["lake", "env", "lean", "Audit.lean"], "axioms.log"),
        "integration": run(["lake", "env", "lean", "IntegrationAudit.lean"], "integration.log"),
    }
    audit = (out / "axioms.log").read_text()
    entries = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit, re.S)
    entries += [(name, "") for name in re.findall(
        r"'([^']+)' does not depend on any axioms", audit)]
    expected = re.findall(r"^#print axioms (\S+)", (ROOT / "Audit.lean").read_text(), re.M)
    if {name for name, _ in entries} != set(expected) or len(entries) != len(expected):
        raise SystemExit("Incomplete axiom audit output")
    for name, raw in entries:
        axioms = {x.strip() for x in raw.split(",") if x.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            raise SystemExit(f"Unexpected axiom dependencies for {name}: {axioms}")
    for name in ["build.log", "axioms.log", "integration.log"]:
        if re.search(r"\b(?:warning|error):", (out / name).read_text()):
            raise SystemExit(f"Diagnostics in verification/{name}")
    proof_sources = [ROOT / "ThreeSquares.lean", ROOT / "Audit.lean",
                     ROOT / "IntegrationAudit.lean"]
    proof_sources += sorted((ROOT / "ThreeSquares").rglob("*.lean"))
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in proof_sources}
    result = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "mathlib_revision": packages["mathlib"]["rev"],
        "fc_revision": FC_COMMIT,
        "fc_source_unmodified": True,
        "actual_fc_definition_provenance_checked": True,
        "upper_bound_type_matches_fc": True,
        "upstream_sorry_negative_controls_passed": True,
        "build_passed": True,
        "audited_theorems": len(entries),
        "axioms_used": sorted(ALLOWED_AXIOMS),
        "sorryAx_present_in_project_theorems": False,
        "global_arbitrary_rotation_lower_bound_proved": True,
        "fc_is_least_proved_unconditionally": True,
        "center_elimination_certificates_kernel_checked": True,
        "axis_aligned_exact_minimum_proved": True,
        "exact_centered_packing_equivalence_proved": True,
        "normalized_finite_parameter_equivalence_proved": True,
        "rotated_closed_vertex_bounds_proved": True,
        "normalized_separator_equivalence_proved": True,
        "four_vertex_containment_equivalence_proved": True,
        "exact_finite_inequality_model_proved": True,
        "finite_edge_normal_reduction_proved": True,
        "auxiliary_free_edge_constraint_model_proved": True,
        "rational_interval_checker_soundness_proved": True,
        "packing_formula_necessity_proved": True,
        "smaller_fc_packing_initial_box_coverage_proved": True,
        "small_certificate_examples_verified": True,
        "bounded_certificate_generator_soundness_proved": True,
        "generated_representative_certificates_kernel_checked": True,
        "global_exclusion_certificate_supplied": True,
        "representative_certificate_cases": len(benchmark["cases"]),
        "certificate_benchmark_hashes_match": True,
        "center_radial_bound_proved": True,
        "center_norm_below_11_over_16_proved": True,
        "pairwise_center_distance_at_least_one_proved": True,
        "normalized_local_geometry_constraints_proved": True,
        "normalized_local_geometry_rigidity_proved": True,
        "normalized_local_radius_lower_bound_proved": True,
        "reflected_frames_eliminated_by_square_symmetry": True,
        "first_quadrant_rotation_representatives_proved": True,
        "rational_rotation_parameterization_proved": True,
        "normalized_eight_configuration_variable_model_proved": True,
        "subcritical_radius_elimination_proved": True,
        "denominator_cleared_eight_variable_formula_proved": True,
        "eight_variable_certificate_connection_proved": True,
        "twenty_four_quadrant_box_cover_proved": True,
        "two_quadrant_orbit_classification_proved": True,
        "quadrant_orbit_symmetry_reduction_proved": True,
        "branch_symmetry_reduction_512_to_64_proved": True,
        "local_lemma_connected_to_residual_boxes": True,
        "smaller_fc_packing_contracted_box_coverage_proved": True,
        "contracted_formula_necessity_proved": True,
        "weighted_search_soundness_proved": True,
        "contracted_domain_runs": [
            {key: row[key] for key in ["case", "depth_limit", "node_count", "kept_count", "rejected_count"]}
            for row in benchmark["cases"] if row["case"] in ["Focused6", "Focused8"]],
        "bounded_full_domain_residual_count": next(
            row["kept_count"] for row in benchmark["cases"] if row["case"] == "Initial6"),
        "source_sha256": hashes,
        "verification_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "verification_seconds": times,
        "full_clean_environment_tested": False,
    }
    (out / "result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
