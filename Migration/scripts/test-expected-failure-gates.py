#!/usr/bin/env python3
"""Exercise both fixture gates against real Lean plus inventory faults.

Run after lake build. Disposable directories share only the built .lake tree;
these are tests of the gate, not clean scientific mutation builds.
"""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent.parent
    if not (repo / '.lake/build').is_dir():
        raise SystemExit('Run lake build before the gate self-tests')
    if not shutil.which('pwsh'):
        raise SystemExit('PowerShell unavailable: this two-gate test cannot pass')
    args.output.mkdir(parents=True, exist_ok=True)
    manifest = (repo / 'scripts/expected-failures.tsv').read_text()
    rows = [line for line in manifest.splitlines() if line and not line.startswith('#')]
    first = rows[0].split('\t')[0]
    cases = [
        ('baseline', None), ('unlisted', 'uninventoried fixture'),
        ('orphan', 'orphan fixture entry'), ('duplicate', 'duplicate fixture'),
        ('compiles', 'unexpectedly compiled'), ('wrong-diagnostic', 'failed for an unexpected reason'),
        ('missing-file', 'orphan fixture entry'), ('interrupted', 'interrupted or timed out'),
    ]
    records = []
    for case, expected in cases:
        with tempfile.TemporaryDirectory(prefix='fixture-gate-') as directory:
            work = Path(directory)
            shutil.copytree(repo / 'Tests/ExpectedFailure', work / 'Tests/ExpectedFailure')
            (work / 'scripts').mkdir()
            for name in ('check-expected-failures.sh', 'check-expected-failures.ps1', 'expected-failures.tsv'):
                shutil.copy2(repo / 'scripts' / name, work / 'scripts' / name)
            os.symlink(repo / '.lake', work / '.lake', target_is_directory=True)
            for config in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
                shutil.copy2(repo / config, work / config)
            inventory = work / 'scripts/expected-failures.tsv'
            environment = dict(os.environ)
            if case == 'unlisted':
                (work / 'Tests/ExpectedFailure/Unlisted.lean.fail').write_text('example : True := True.intro\n')
            elif case == 'orphan':
                inventory.write_text(manifest + 'Tests/ExpectedFailure/Absent.lean.fail\tdependent-type\tType mismatch\n')
            elif case == 'duplicate':
                inventory.write_text(manifest + rows[0] + '\n')
            elif case == 'compiles':
                (work / first).write_text('example : True := True.intro\n')
            elif case == 'wrong-diagnostic':
                inventory.write_text(manifest.replace(rows[0], '\t'.join(rows[0].split('\t')[:2]) + '\tIMPOSSIBLE_EXPECTED_DIAGNOSTIC'))
            elif case == 'missing-file':
                (work / first).unlink()
            elif case == 'interrupted':
                # Simulates a process-level interruption, never a Lean proof result.
                binary = work / 'bin'; binary.mkdir()
                (binary / 'lake').write_text('#!/usr/bin/env sh\nexit 124\n')
                (binary / 'lake').chmod(0o755)
                environment['PATH'] = str(binary) + os.pathsep + environment['PATH']
            for surface, command in (
                ('bash', ['bash', 'scripts/check-expected-failures.sh']),
                ('powershell', ['pwsh', '-NoProfile', '-File', 'scripts/check-expected-failures.ps1']),
            ):
                result = subprocess.run(command, cwd=work, env=environment, capture_output=True, text=True, timeout=180)
                text = result.stdout + result.stderr
                log = args.output / f'{case}-{surface}.log'
                log.write_text(text)
                executed = [line.split('\t')[-1] for line in text.splitlines() if line.startswith('EXPECTED_FAILURE_OK\t')]
                passed = (result.returncode == 0 and len(executed) == len(rows) and len(set(executed)) == len(rows)) if case == 'baseline' else (result.returncode != 0 and expected in text)
                records.append(dict(case=case, surface=surface, exit_code=result.returncode, passed=passed, fixture_calls=len(executed), log=log.name))
                print(case, surface, result.returncode, 'PASS' if passed else 'FAIL', flush=True)
    (args.output / 'results.json').write_text(json.dumps(records, indent=2))
    if not all(record['passed'] for record in records):
        raise SystemExit('Fixture-gate self-test failed')

if __name__ == '__main__':
    main()
