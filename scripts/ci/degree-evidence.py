"""DO NOT MERGE: one disposable hosted DegreePolyTime measurement, #5432/#5557."""
import ctypes
import difflib
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time
import tomllib

sys.path.insert(0, str(Path.cwd() / 'scripts/cache'))
from bounded import stop_group, interruptible

BASE = '53054f4d119d41774b1f9a02a04e6188f5e3b502'
TARGET = 'ef1d1d095af3bc58a35ee27ba4b1c8d8a998acad'
SOURCE = Path('CslibFrontierTests/DegreePolyTime.lean')
NAMES = [prefix + kind for prefix in ('explicit', 'transition')
         for kind in ('Pack', 'Flag', 'Composition')]
# Normal regression sources stay silent under --iofail. Add scoped profiling
# and explicit command totals only in the disposable hosted copy.
WRAPPER = '''
set_option Elab.async false
open Lean Elab Command in
elab "degree_measure " label:str cmd:command : command => do
  logInfo m!"DEGREE_BEGIN {label.getString}"
  let start ← IO.monoNanosNow
  elabCommand cmd
  let stop ← IO.monoNanosNow
  logInfo m!"DEGREE_TOTAL {label.getString} {stop - start}"
  logInfo m!"DEGREE_END {label.getString}"

'''


def run(args, out, label, timeout=900, cwd=None):
    """Bound the owned process group, including children surviving leader exit."""
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(36, 1, 0, 0, 0) != 0:
        raise OSError('cannot enable owned descendant reaping')
    start = time.monotonic()
    code, timed_out, failure = 125, False, None
    try:
        with (out / (label + '.log')).open('wb') as log:
            proc = subprocess.Popen(args, cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                                    start_new_session=True)
            try:
                code = proc.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                code = 124
            finally:
                # Repository-tested TERM/KILL/subreap/absence verification.
                stop_group(proc, grace=5)
    except BaseException as error:
        code, failure = 125, repr(error)
        raise
    finally:
        row = dict(command=args, status=code, timeout=timed_out, failure=failure,
                   elapsed_seconds=time.monotonic() - start)
        (out / (label + '.status.json')).write_text(json.dumps(row, indent=2))
    if code:
        raise RuntimeError(f'{label} failed: {code}')
    return (out / (label + '.log')).read_text()


def instrument(source, diagnostic=False):
    assert source.count('fail_if_success fun_prop') == 2, 'negative controls changed'
    assert 'set_option trace.profiler true' not in source, 'target should be silent'
    assert source.count('private theorem ') == 8, 'unexpected source declarations'
    text = source.replace('namespace CslibFrontierTests.DegreePolyTime',
                          WRAPPER + 'namespace CslibFrontierTests.DegreePolyTime', 1)
    text = text.replace('import CslibFrontier.', 'import Lean\n\nimport CslibFrontier.', 1)
    for name in NAMES:
        needle = 'private theorem ' + name
        assert text.count(needle) == 1, name
        text = text.replace(needle, f'degree_measure "{name}"\nset_option trace.profiler true in\n' + needle)
    # Identify the separate degree-composition goal and both controls without
    # changing their statements, tactics, registration, or section boundaries.
    for needle, label in [
        ('example (d e k : ℕ) :\n    ComputableInDegree', 'degreeComposition'),
        ('example (d e : ℕ) : ComputableInPolyTime', 'beforeControl'),
        ('example : ComputableInPolyTime (pack 2 0)', 'afterControl')]:
        assert text.count(needle) == 1, label
        text = text.replace(needle, f'degree_measure "{label}"\n' + needle)
    if diagnostic:
        text = text.replace('\n  fun_prop\n', '\n  show_term fun_prop\n')
    assert text.count('fail_if_success fun_prop') == 2
    return text


def intervals(log):
    result = {}
    for label in [*NAMES, 'degreeComposition', 'beforeControl', 'afterControl']:
        begin = list(re.finditer(r'DEGREE_BEGIN ' + label + r'\b', log))
        end = list(re.finditer(r'DEGREE_END ' + label + r'\b', log))
        assert len(begin) == len(end) == 1 and begin[0].end() < end[0].start(), label
        block = log[begin[0].end():end[0].start()]
        totals = re.findall(r'DEGREE_TOTAL ' + label + r' (\d+)\b', block)
        assert len(totals) == 1 and int(totals[0]) > 0, label
        result[label] = dict(nanoseconds=int(totals[0]), raw_interval=block)
    return result


def routes(rows):
    # show_term emits the successful proof, unlike trace messages about attempted
    # rules. Require it for each route; never accept mere names in search traces.
    for name, required in {
        'transitionPack': ['computableInPolyTime', 'pack_deg'],
        'transitionFlag': ['computableInPolyTime', 'flag_deg'],
        'transitionComposition': ['computableInPolyTime', 'pack_deg', 'flag_deg'],
        'degreeComposition': ['comp', 'pack_deg', 'flag_deg'],
    }.items():
        block = rows[name]['raw_interval']
        # Pinned Hint.mkSuggestionsMessage renders a newline and indented
        # suggestion. Never scan past that suggestion into attempted-rule traces.
        proofs = re.findall(
            r'^Try this:[ \t]*\n[ \t]+exact ([^\n]*'
            r'(?:\n[ \t]+(?![ \t]*\[)[^\n]+)*)', block, re.M)
        assert len(proofs) == 1, f'missing/ambiguous successful proof: {name}'
        assert all(re.search(r'\b' + word + r'\b', proofs[0]) for word in required), name


def flatten(table, prefix=''):
    for key, value in table.items():
        key = prefix + key
        if isinstance(value, dict):
            yield from flatten(value, key + '.')
        else:
            yield f'-D{key}={str(value).lower()}'


def main():
    assert os.environ.get('GITHUB_ACTIONS') == 'true', 'hosted only'
    out = Path(os.environ['RUNNER_TEMP']) / 'degree-evidence'
    out.mkdir(exist_ok=False)
    assert run(['git', 'rev-parse', 'HEAD'], out, 'head').strip() == TARGET
    assert Path('lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.36.0-rc2'
    (out / 'bounded.py').write_bytes(Path('scripts/cache/bounded.py').read_bytes())
    harness = Path(__file__).resolve().parents[2]
    harness_sha = run(['git', '-C', str(harness), 'rev-parse', 'HEAD'], out, 'harness-head').strip()
    assert harness_sha == os.environ['GITHUB_SHA'], 'instrumentation revision mismatch'
    for relative in ['scripts/ci/degree-evidence.py', '.github/workflows/lean_action_ci.yml']:
        (out / Path(relative).name).write_bytes((harness / relative).read_bytes())
    assert not run(['git', 'status', '--porcelain', '--untracked-files=no'], out, 'source-clean').strip()
    original = SOURCE.read_text()
    (out / 'original.lean').write_text(original)
    metadata = dict(target=TARGET, instrumentation_base=BASE, instrumentation_sha=harness_sha, toolchain=Path('lean-toolchain').read_text(),
                    machine=platform.uname()._asdict(), cpu=Path('/proc/cpuinfo').read_text(),
                    runner_image=os.environ.get('ImageVersion'), order=NAMES,
                    source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                    limits='Single ordered run; warm dependencies, no statistical inference. Nanosecond clock units are not accuracy. Command totals include profiler overhead, no fun_prop tracing. Never infer statement totals from whole-file elapsed time.')
    (out / 'metadata.json').write_text(json.dumps(metadata, indent=2))
    run(['scripts/cache/ensure.sh'], out, 'bootstrap', 900)
    run(['lake', 'build', '--wfail', '--iofail', 'CslibFrontierTests.DegreePolyTime'], out, 'strict-build', 3600)
    flags = list(flatten(tomllib.loads(Path('lakefile.toml').read_text())['leanOptions']))
    common = ['lake', 'env', 'lean', *flags, '-DwarningAsError=true', '-Dtrace.profiler.threshold=0']
    # Required exact-source direct pass first; no cached target substitutes for it.
    run([*common, str(SOURCE)], out, 'exact-source')
    try:
        for label, diagnostic in [('timing', False), ('diagnostic', True)]:
            modified = instrument(original, diagnostic)
            (out / (label + '.diff')).write_text(''.join(difflib.unified_diff(
                original.splitlines(True), modified.splitlines(True), fromfile=str(SOURCE), tofile=str(SOURCE))))
            (out / (label + '.lean')).write_text(modified)
            # Atomic replacement avoids writing through any shared-cache inode.
            tmp = SOURCE.with_suffix('.degree-tmp')
            tmp.write_text(modified)
            tmp.replace(SOURCE)
            args = [*common]
            if diagnostic:
                args += ['-Dtrace.Meta.Tactic.fun_prop=true']
            rows = intervals(run([*args, str(SOURCE)], out, label))
            (out / (label + '.intervals.json')).write_text(json.dumps(rows, indent=2))
            if diagnostic:
                routes(rows)
            else:
                timing = rows
        comparisons = {kind: {prefix: timing[prefix + kind]['nanoseconds']
                               for prefix in ('explicit', 'transition')}
                       for kind in ('Pack', 'Flag', 'Composition')}
        (out / 'comparisons.json').write_text(json.dumps(comparisons, indent=2))
        (out / 'ACCEPTED').write_text('All intervals, expanded routes and both scoped negative controls checked. Single-run observations only.\n')
    finally:
        tmp = SOURCE.with_suffix('.degree-tmp')
        tmp.write_text(original)
        tmp.replace(SOURCE)


if __name__ == '__main__':
    with interruptible():
        main()
