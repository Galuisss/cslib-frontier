"""Disposable hosted comparison for #5475; adapted from #5530 and #5478. DO NOT MERGE. No local execution."""
import hashlib
import json
import os
import signal
from pathlib import Path
import statistics
import subprocess
import time
import tomllib
from hierarchy_evidence_support import restore_snapshot

VARIANTS = {
    'before': '39b11c9de0f10903a504a027fea5636708f7be6d',
    'after': '32b096e9f3f1a0bb6d39ff88c4b7ac9da29ac908',
}
ROOT = 'CslibFrontier/DataStructure/Dictionary/WordRAM/'
# ValidHistory uses changed private definitions through import all.
CLIENTS = ['SuccinctSlabPool', 'SuccinctSlabMove', 'SuccinctSlabOps',
           'SuccinctMicroChain', 'SuccinctValidHistory']
MODULES = CLIENTS
OUT = Path(os.environ['RUNNER_TEMP']) / 'succinct-evidence'
OUT.mkdir(parents=True, exist_ok=True)

def run(args, **kw):
    print('+', ' '.join(map(str, args)), flush=True)
    return subprocess.run(args, check=True, **kw)

def flatten(table, prefix=''):
    for name, value in table.items():
        key = f'{prefix}.{name}' if prefix else name
        if isinstance(value, dict):
            yield from flatten(value, key)
        else:
            yield key, value

# Only disposable hosted checkout changes; no worktrees/shared object manipulation.
resolved = {k: subprocess.check_output(['git', 'rev-parse', v], text=True).strip()
            for k, v in VARIANTS.items()}
for config in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
    contents = [subprocess.check_output(['git', 'show', f'{sha}:{config}']) for sha in resolved.values()]
    assert all(c == contents[0] for c in contents), config
metadata = dict(commits=resolved, warmups=1, repetitions=5,
                cpu=Path('/proc/cpuinfo').read_text(),
                limits='900s each; whole-module startup/import/elaboration/output wall time. Setup/builds excluded; no heartbeat overrides. Same toolchain/dependency pins/options; revision-specific warm imports. Not a preservation audit or full CI validation.')
(OUT / 'metadata.json').write_text(json.dumps(metadata, indent=2))
setups = {}
flags = []
# Prepare every variant once before timing. Preserve independent outputs by copying
# the dictionary output subtree; dependency packages stay fixed throughout.
for label, sha in resolved.items():
    run(['git', 'restore', '--source', sha, '--', 'CslibFrontier', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'])
    run(['scripts/cache/ensure.sh'])
    dest = OUT / label
    dest.mkdir()
    modules = [ROOT + n + '.lean' for n in MODULES]
    assert all(Path(p).is_file() for p in modules)
    # Both variants must compile before ANY timing.
    with (dest / 'build.log').open('w') as log:
        run(['lake', 'build', '--wfail', '--iofail', *[p[:-5].replace('/', '.') for p in modules]],
            stdout=log, stderr=subprocess.STDOUT)
    for name in CLIENTS:
        p = ROOT + name + '.lean'
        result = run(['lake', 'setup-file', p], capture_output=True, text=True)
        json.loads(result.stdout)
        setup = dest / (name + '.setup.json')
        setup.write_text(result.stdout)
        (dest / (name + '.setup.stderr')).write_text(result.stderr)
        setups[label, name] = setup
    for p in modules:
        (dest / Path(p).name).write_bytes(Path(p).read_bytes())
    # Include all changed dictionary imports and private import-all artifacts.
    snapshot = dest / 'lib' / Path(ROOT)
    snapshot.parent.mkdir(parents=True, exist_ok=True)
    run(['cp', '-a', '--reflink=auto', str(Path('.lake/build/lib/lean') / ROOT), str(snapshot)])
    flags = [f'-D{k}={str(v).lower()}' for k, v in flatten(tomllib.loads(Path('lakefile.toml').read_text())['leanOptions'])]

rows = []
for rep in range(6):
    labels = list(resolved)
    if rep % 2:
        labels.reverse()
    for label in labels:
        sha = resolved[label]
        run(['git', 'restore', '--source', sha, '--', 'CslibFrontier'])
        # Setup JSON names root outputs here; restore that variant's compiled imports.
        restore_snapshot(OUT / label / 'lib', '.lake/build/lib/lean')
        for name in CLIENTS:
            p = ROOT + name + '.lean'
            dest = OUT / f'{name}-{label}-{rep}'
            dest.mkdir()
            cmd = ['lake', 'env', 'lean', '--setup', str(setups[label, name]), *flags,
                   '-o', str(dest / 'result.olean'), '-i', str(dest / 'result.ilean'), p]
            start = time.perf_counter()
            with (dest / 'lean.log').open('w') as log:
                # Lake env spawns Lean: bound the entire invocation process group.
                with subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT,
                                      start_new_session=True) as process:
                    try:
                        returncode = process.wait(timeout=900)
                    except subprocess.TimeoutExpired:
                        try:
                            os.killpg(process.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        process.wait()
                        returncode = 124
            row = dict(module=name, variant=label, sha=sha, repetition=rep, warmup=rep == 0,
                       seconds=time.perf_counter()-start, returncode=returncode,
                       source_sha256=hashlib.sha256(Path(p).read_bytes()).hexdigest(), command=cmd)
            rows.append(row)
            (OUT / 'timings.json').write_text(json.dumps(rows, indent=2))
            print(json.dumps(row), flush=True)
            if returncode:
                raise SystemExit(returncode)
summary = []
for name in CLIENTS:
    for label in resolved:
        xs = [r['seconds'] for r in rows if r['module'] == name and r['variant'] == label and not r['warmup']]
        summary.append(dict(module=name, variant=label, samples=xs, median=statistics.median(xs), minimum=min(xs), maximum=max(xs)))
(OUT / 'summary.json').write_text(json.dumps(summary, indent=2))
