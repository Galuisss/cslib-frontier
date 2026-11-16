"""Disposable targeted import-minimization evidence for #5822. DO NOT MERGE."""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

TARGET = 'ae3fcd1c14da7d291d9589bf63c0de8e74dd10c3'
BASE = '11fd8ab3cd273f2b60ce90e820d70cb23d5b7ffa'
PREFIX = 'CslibFrontier.Computability.Machines.Turing.MultiTape.'
MODULES = [
    'CslibFrontier.Computability.Complexity.FineGrained.Diameter',
    'CslibFrontier.Computability.Complexity.Reduction.Autoreducibility',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.DivConq',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Encoding',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Cases',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Doubled',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.SmallSpace',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Routines',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Primitives',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Decode',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Translate',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Basic',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.MultiPass',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeClosure',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayInput',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.InPlace',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.WindowedInit',
    'CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.WindowedParts',
    'CslibFrontierTests.LinearCodecs',
    'CslibFrontierTests.Quantitative',
    'CslibFrontierTests.Williams',
]


def run(args, out, label, timeout, required=True):
    """Keep the command, complete merged log, status and bound its whole process group."""
    start = time.monotonic()
    status = None
    timed_out = False
    with (out / (label + '.log')).open('w') as log:
        with subprocess.Popen(args, stdout=log, stderr=subprocess.STDOUT,
                              start_new_session=True) as proc:
            try:
                status = proc.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
                status = 124
    (out / (label + '-status.json')).write_text(json.dumps(dict(
        command=args, returncode=status, timeout_seconds=timeout, timed_out=timed_out,
        elapsed_seconds=time.monotonic() - start), indent=2))
    if status and required:
        raise RuntimeError(f'{label} returned status {status}; inspect the retained raw log')

    return status


def shake_command():
    # The strict inventory build validates these roots and their dependency closure.
    # --only limits minimization; other reachable modules may still get add-only suggestions.
    # --force skips Lake's unrelated workspace-default-target no-build preflight only.
    # Pinned cslib documents the first three policy flags. keep-public additionally
    # preserves every explicit public import (Shake.visitModule), without rewriting sources.
    args = ['lake', 'shake', '--add-public', '--keep-implied', '--keep-prefix',
            '--keep-public', '--force', '--explain']
    for module in MODULES:
        args += ['--only', module]
    return args + MODULES


def main():
    out = Path(os.environ['RUNNER_TEMP']) / 'imports-evidence'
    out.mkdir(exist_ok=False)
    harness = Path(__file__).resolve().parents[2]
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
    harness_head = subprocess.check_output(
        ['git', '-C', str(harness), 'rev-parse', 'HEAD'], text=True).strip()
    assert head == TARGET, 'unexpected target'
    assert harness_head == os.environ['GITHUB_SHA'], 'unexpected harness'
    # The nested harness is untracked; tracked target sources must start and end pristine.
    assert not subprocess.check_output(
        ['git', 'status', '--porcelain', '--untracked-files=no'], text=True).strip()
    files = [name.replace('.', '/') + '.lean' for name in MODULES]
    files += ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
              'scripts/check_tidy_usage.py', 'scripts/lean_outputs.py',
              'scripts/LeanOutputs.lean', 'scripts/proof_lengths.py',
              'scripts/build.sh', 'scripts/cache/ensure.sh']
    files += sorted(str(p) for root in ['CslibFrontier', 'CslibFrontierTests', 'guide']
                    for p in Path(root).rglob('*.lean') if '.lake' not in p.parts)
    files += ['CslibFrontier.lean']
    files = sorted(set(files))
    manifest = {f: hashlib.sha256(Path(f).read_bytes()).hexdigest() for f in files}
    for name in ['scripts/ci/imports-evidence.py', '.github/workflows/lean_action_ci.yml']:
        (out / Path(name).name).write_bytes((harness / name).read_bytes())
    tool_sources = Path.home() / '.elan/toolchains' / (Path('lean-toolchain').read_text().strip()
        .replace('/', '--').replace(':', '---')) / 'src/lean/lake/Lake/CLI'
    for name in ['Main.lean', 'Shake.lean']:
        (out / ('lake-' + name)).write_bytes((tool_sources / name).read_bytes())
    (out / 'metadata.json').write_text(json.dumps(dict(
        target=head, harness=harness_head, harness_base=BASE, modules=MODULES,
        source_sha256=manifest,
        harness_sha256={name: hashlib.sha256((harness / name).read_bytes()).hexdigest()
            for name in ['scripts/ci/imports-evidence.py', '.github/workflows/lean_action_ci.yml']},
        tool_sha256={name: hashlib.sha256((tool_sources / name).read_bytes()).hexdigest()
            for name in ['Main.lean', 'Shake.lean']}, run_id=os.environ.get('GITHUB_RUN_ID'),
        interpretation='Raw tool suggestions, not automatic removal approval. Public imports are '
        'preserved; no --fix. Status 1 can mean suggestions or an error; inspect the raw log. '
        'A successful command is not evidence that suggestions are empty.'
    ), indent=2))
    # check_outputs requires ROOTS' complete physical inventory and Lake freshness.
    # Do not narrow ROOTS or bypass freshness. Bootstrap is included, hosted only.
    run(['scripts/build.sh', 'CslibFrontier', 'CslibFrontierTests', '--wfail', '--iofail'],
        out, 'strict-build', 4800)
    for package in ['cslib', 'importGraph']:
        run(['git', '-C', '.lake/packages/' + package, 'rev-parse', 'HEAD'],
            out, package + '-revision', 30, required=False)
    try:
        tidy_status = run(['python3', '-B', 'scripts/check_tidy_usage.py',
            '--json', str(out / 'tidy-usage.json'),
            '--markdown', str(out / 'tidy-usage.md')], out, 'tidy-usage', 1800, required=False)
        shake_status = run(shake_command(), out, 'import-minimization', 1800, required=False)
        # Default report excludes the native kernel. Retain a supplementary unexcluded
        # view so those internal rows are measured rather than silently treated as zero.
        native_status = run(['python3', '-B', 'scripts/check_tidy_usage.py',
            '--internal-prefix', '__no_matching_measurement_boundary__/',
            '--json', str(out / 'tidy-usage-unexcluded.json'),
            '--markdown', str(out / 'tidy-usage-unexcluded.md')],
            out, 'tidy-usage-unexcluded', 1800, required=False)
        (out / 'assessment-status.json').write_text(json.dumps(
            dict(tidy_usage=tidy_status, import_minimization=shake_status, native=native_status), indent=2))
    finally:
        # Suggestions commonly return 1. Retain source identity even on that nonzero result;
        # the raw status/log, not the job colour, determines suggestions versus a tool error.
        run(['git', 'diff', '--exit-code'], out, 'source-diff', 30)
        final = {f: hashlib.sha256(Path(f).read_bytes()).hexdigest() for f in files}
        assert final == manifest, 'target sources changed'
        assert not subprocess.check_output(
            ['git', 'status', '--porcelain', '--untracked-files=no'], text=True).strip()
        (out / 'source-identity.json').write_text(json.dumps(final, indent=2))
    (out / 'COMPLETED').write_text('Both assessments attempted after strict inventory build. '
        'Inspect assessment-status.json and raw logs; status 1 is not an assessment verdict.\n')
    if tidy_status != 0 or native_status != 0 or shake_status not in (0, 1):
        raise RuntimeError('Assessment error; retained evidence is incomplete')


if __name__ == '__main__':
    main()
