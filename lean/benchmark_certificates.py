#!/usr/bin/env python3
"""Regenerate representative certificates and measure independent Lean checks.

Native execution proposes data, and JSON records are not proofs. The generated
Lean files use `decide +kernel` on the actual shared packing formula. Reported
verification time includes Lean startup, imports, elaboration and kernel checks.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'certificates'


def run(args, name):
    start = time.perf_counter()
    env = os.environ.copy()
    env.setdefault('LEAN_NUM_THREADS', '4')
    with (OUT / name).open('w') as log:
        result = subprocess.run(args, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode or re.search(r'\b(?:error|warning):', (OUT / name).read_text()):
        raise SystemExit(f'Failed: {args}; see certificates/{name}')
    return round(time.perf_counter() - start, 3)


def hashes(paths):
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def main():
    OUT.mkdir(exist_ok=True)
    run(['lake', '--wfail', 'build', 'ThreeSquares.WeightedSearch',
         'ThreeSquares.ContractedSyntax'], 'dependencies.log')
    generation_seconds = run(['lake', 'env', 'lean', '--run', 'GenerateCertificates.lean'],
                             'generation.log')
    rows = json.loads((OUT / 'generation.json').read_text())
    files = [ROOT / r['source_file'] for r in rows]
    files += [OUT / f"{r['case']}-residuals.json" for r in rows]
    files += [ROOT / 'ThreeSquares/GeneratedCertificates.lean']
    first = hashes(files)
    run(['lake', 'env', 'lean', '--run', 'GenerateCertificates.lean'], 'regeneration.log')
    if first != hashes(files):
        raise SystemExit('Certificate or residual data changed on repeated generation')
    for row in rows:
        name = row['case']
        row['lean_verification_seconds_including_imports'] = run(
            ['lake', 'env', 'lean', row['source_file']], f'{name}-kernel.log')
        row['kernel_checked'] = True
        residuals = json.loads((OUT / f'{name}-residuals.json').read_text())
        if len(residuals) != row['kept_count']:
            raise SystemExit(f'Residual count mismatch: {name}')
        print(json.dumps(row, ensure_ascii=False), flush=True)
    result = {
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'generation_process_seconds': generation_seconds,
        'repeated_generation_identical': True,
        'native_execution_used_as_proof': False,
        'verification_timing_includes_startup_imports_elaboration': True,
        'global_lower_bound_proved': False,
        'cases': rows,
        'artifact_sha256': first,
        'generator_sha256': hashes([ROOT / 'GenerateCertificates.lean',
            ROOT / 'ThreeSquares/CertificateSearch.lean', ROOT / 'ThreeSquares/PackingSyntax.lean',
            ROOT / 'ThreeSquares/WeightedSearch.lean', ROOT / 'ThreeSquares/ContractedSyntax.lean',
            ROOT / 'benchmark_certificates.py']),
    }
    (OUT / 'benchmark.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')


if __name__ == '__main__':
    main()
