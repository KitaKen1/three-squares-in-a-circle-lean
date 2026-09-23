#!/usr/bin/env python3
"""Build the compressed FC proof in dependency order, then audit its target.

Lake checks source/dependency changes on every invocation; its existing caches
are reused. This is not a zero-cache rebuild. No Python certificate generator
or floating-point computation is needed to verify the delivered Lean sources.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
TARGET = "ThreeSquares.Compressed.Main"


def closure(module, seen, ordered):
    if module in seen:
        return
    seen.add(module)
    source = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
    for dep in re.findall(r"^import\s+([\w.]+)", source.read_text(), re.M):
        if dep.startswith("ThreeSquares."):
            closure(dep, seen, ordered)
    ordered.append((module, source))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", action="store_true", help="List modules without running Lean")
    args = parser.parse_args()
    modules = []
    closure(TARGET, set(), modules)
    if args.plan:
        print("\n".join(name for name, _ in modules))
        print("Audit: CompressedAudit.lean")
        return

    report_dir = ROOT / "verification/compressed-rebuild"
    report_dir.mkdir(parents=True, exist_ok=True)
    report = {
        "started_at_utc": datetime.now(timezone.utc).isoformat(),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "manifest_sha256": digest(ROOT / "lake-manifest.json"),
        "scope": "Sequential Lake targets, with dependency caches reused; followed by actual-FC audit",
        "source_sha256": {str(p.relative_to(ROOT)): digest(p) for _, p in modules},
        "complete": False,
        "checks": [],
    }
    report["source_sha256"]["CompressedAudit.lean"] = digest(ROOT / "CompressedAudit.lean")
    jobs = [(name, ["lake", "build", "+" + name]) for name, _ in modules]
    jobs.append(("CompressedAudit", ["lake", "env", "lean", "-M6144", "CompressedAudit.lean"]))
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    for i, (name, command) in enumerate(jobs, 1):
        print(f"[{i}/{len(jobs)}] {name}", flush=True)
        logfile = report_dir / (name + ".log")
        started = time.monotonic()
        with logfile.open("w") as log:
            proc = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        report["checks"].append({
            "module": name, "command": command, "exit": proc.returncode,
            "seconds": round(time.monotonic() - started, 3),
            "log": str(logfile.relative_to(ROOT)),
        })
        report["complete"] = proc.returncode == 0 and i == len(jobs)
        (report_dir / "result.json").write_text(json.dumps(report, indent=2) + "\n")
        if proc.returncode:
            print(logfile.read_text()[-12000:])
            raise SystemExit(f"Failed: {name}; see {logfile}")
        if name == "CompressedAudit":
            print(logfile.read_text())
    print(f"Compressed FC proof and audit passed. Record: {report_dir / 'result.json'}")


if __name__ == "__main__":
    main()
