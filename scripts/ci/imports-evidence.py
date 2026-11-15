"""Disposable targeted import-minimization evidence for #5568. DO NOT MERGE."""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

TARGET = 'f1394960ce04d60473ccec78b4cc67b92fae55a6'
BASE = '43199b2ea7edb8b5af0e81815ea18e9c77a8d0b9'
PREFIX = 'CslibFrontier.Computability.Machines.Turing.MultiTape.'
MODULES = [PREFIX + name for name in [
    'Complexity.Streaming',
    'Complexity.BigO.Constructible',
    'Internal.NormalForm',
]]


def run(args, out, label, timeout):
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
    (out / (label + '.json')).write_text(json.dumps(dict(
        command=args, returncode=status, timeout_seconds=timeout, timed_out=timed_out,
        elapsed_seconds=time.monotonic() - start), indent=2))
    if status:
        raise RuntimeError(f'{label} returned status {status}; inspect the retained raw log')


def shake_command():
    # The preceding strict targeted build validates these roots and their dependency closure.
    # --force skips Lake's unrelated workspace-default-target no-build preflight only.
    args = ['lake', 'shake', '--force', '--explain', '--keep-public']
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
    files += ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
    manifest = {f: hashlib.sha256(Path(f).read_bytes()).hexdigest() for f in files}
    for name in ['scripts/ci/imports-evidence.py', '.github/workflows/lean_action_ci.yml']:
        (out / Path(name).name).write_bytes((harness / name).read_bytes())
    (out / 'metadata.json').write_text(json.dumps(dict(
        target=head, harness=harness_head, harness_base=BASE, modules=MODULES,
        source_sha256=manifest, run_id=os.environ.get('GITHUB_RUN_ID'),
        interpretation='Raw tool suggestions, not automatic removal approval. Public imports are '
        'preserved; no --fix. Status 1 can mean suggestions or an error; inspect the raw log. '
        'A successful command is not evidence that suggestions are empty.'
    ), indent=2))
    # Targeted strict build includes the standard cache bootstrap, only on the hosted runner.
    run(['scripts/build.sh', *MODULES, '--wfail', '--iofail'], out, 'strict-build', 3600)
    try:
        run(shake_command(), out, 'import-minimization', 1800)
    finally:
        # Suggestions commonly return 1. Retain source identity even on that nonzero result;
        # the raw status/log, not the job colour, determines suggestions versus a tool error.
        run(['git', 'diff', '--exit-code'], out, 'source-diff', 30)
        final = {f: hashlib.sha256(Path(f).read_bytes()).hexdigest() for f in files}
        assert final == manifest, 'target sources changed'
        assert not subprocess.check_output(
            ['git', 'status', '--porcelain', '--untracked-files=no'], text=True).strip()
        (out / 'source-identity.json').write_text(json.dumps(final, indent=2))
    (out / 'COMPLETED').write_text('Strict targeted build and read-only minimizer completed. '
        'Inspect import-minimization.log for suggestions before disposition.\n')


if __name__ == '__main__':
    main()
