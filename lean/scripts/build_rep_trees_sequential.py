#!/usr/bin/env python3
"""Build the 16 large representative-tree Lean modules one at a time.

This keeps the proof-certificate workload out of a single large Lake target
build. Lake reuses already-built targets, so rerunning this script resumes
naturally after an interruption. Each module gets its own log and a source
hash in the summary JSON.
"""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
VERIFY = ROOT / "verification"
SUMMARY = VERIFY / "rep-tree-build-summary.json"


def now():
    return datetime.now(timezone.utc).isoformat()


def main():
    VERIFY.mkdir(exist_ok=True)
    try:
        report = json.loads(SUMMARY.read_text())
    except FileNotFoundError:
        report = {
            "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "strategy": "one Lake module target at a time; LEAN_NUM_THREADS=1",
            "modules": [],
        }

    by_module = {row["module"]: row for row in report["modules"]}
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"

    for i in range(16):
        module = f"ThreeSquares.RepTrees.Part{i:02d}"
        source = ROOT / (module.replace(".", "/") + ".lean")
        log_path = VERIFY / f"rep-tree-Part{i:02d}.log"
        command = ["lake", "--wfail", "build", f"+{module}"]
        start = time.monotonic()
        started_at = now()
        print(f"START {module} ({started_at})", flush=True)

        with log_path.open("w") as log:
            proc = subprocess.Popen(
                command, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, text=True, bufsize=1,
            )
            assert proc.stdout is not None
            for line in proc.stdout:
                log.write(line)
                log.flush()
                print(line, end="", flush=True)
            code = proc.wait()

        row = {
            "module": module,
            "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "started_at_utc": started_at,
            "finished_at_utc": now(),
            "elapsed_seconds": round(time.monotonic() - start, 3),
            "exit_code": code,
            "log": str(log_path.relative_to(ROOT)),
        }
        by_module[module] = row
        report["modules"] = [by_module[f"ThreeSquares.RepTrees.Part{j:02d}"]
                             for j in sorted(
                                 int(name.rsplit("Part", 1)[1])
                                 for name in by_module)]
        report["updated_at_utc"] = now()
        SUMMARY.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
        if code:
            raise SystemExit(f"Build failed for {module}; see {log_path}")
        print(f"DONE {module}: {row['elapsed_seconds']}s", flush=True)

    print(f"All 16 representative-tree modules passed; see {SUMMARY}")


if __name__ == "__main__":
    main()
