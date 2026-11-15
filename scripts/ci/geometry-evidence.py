"""Disposable #5746 measurement, adapted from succinct-evidence.py. DO NOT MERGE.
Whole-source kernel-sensitive elaboration proxy, not isolated per-row attribution.
No proof instrumentation or replacement; no performance verdict is automated.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time
import tomllib

VARIANTS = {'before': '1640f9c0c511b5937af478f0b7876e57ca9d0cda',
            'after': '150937e27ccf29aef7c1c872e175a669daf156d2'}
MAIN = 'd83c776472ed326ae2201ee4a61828bedc676093'
ROOT = 'CslibFrontier/Computability/Complexity/Problems/SAT/Planar/'
CLIENTS = {'CrossoverLayoutChecks': 154, 'PairedCrossoverLayoutChecks': 162,
           'OrdinaryRing': 16}

def flatten(table, prefix=''):
    for name, value in table.items():
        key = f'{prefix}.{name}' if prefix else name
        if isinstance(value, dict):
            yield from flatten(value, key)
        else:
            yield key, value

def certificates(source, count):
    rows = re.findall(r'private theorem row_(\d+)\b.*?:= by decide \+kernel', source, re.S)
    assert list(map(int, rows)) == list(range(count)), (len(rows), count)
    assert 'native_decide' not in source
    return rows

def run(args, cwd, dest, env, timeout=900):
    """Same own-process-group bound as succinct; retain start/status even on failure."""
    dest.mkdir(parents=True)
    record = dict(command=list(map(str, args)), cwd=str(cwd), timeout=timeout,
                  started=time.time(), environment_overrides=env)
    (dest/'command.json').write_text(json.dumps(record, indent=2))
    start = time.perf_counter()
    with (dest/'stdout').open('w') as stdout, (dest/'stderr').open('w') as stderr:
        with subprocess.Popen(args, cwd=cwd, env={**os.environ, **env},
                              stdout=stdout, stderr=stderr, start_new_session=True) as process:
            try:
                code = process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
                code = 124
    record.update(returncode=code, seconds=time.perf_counter()-start)
    (dest/'status.json').write_text(json.dumps(record, indent=2))
    print(json.dumps(record), flush=True)
    if code:
        raise SystemExit(code)
    return (dest/'stdout').read_text()

def main():
    workspace = Path.cwd().resolve()
    out = Path(os.environ['RUNNER_TEMP'])/'geometry-evidence'
    out.mkdir()
    metadata = dict(commits=VARIANTS, main_at_preparation=MAIN, warmups=1, repetitions=3,
                    cpu=Path('/proc/cpuinfo').read_text(), uname=list(os.uname()),
                    github={k:os.environ.get(k) for k in ['GITHUB_SHA','GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT']},
                    driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                    limits='Whole-source startup/import/elaboration/output wall time and process-tree maxRSS proxy, not sum RSS or per-row attribution. Setup/build excluded. One warmup plus three alternating pairs. No significance or nonregression verdict; review raw evidence. No heartbeat overrides or proof changes.')
    (out/'metadata.json').write_text(json.dumps(metadata, indent=2))
    setups, flags, envs, sources = {}, {}, {}, {}
    configs = {}
    for label, sha in VARIANTS.items():
        cwd = workspace/f'source-{label}'
        # Distinct package trees, build trees and Lake artifact stores, never symlinked.
        env = {'LAKE_CACHE_DIR': str(out.parent/f'geometry-lake-cache-{label}')}
        envs[label] = env
        actual = run(['git','rev-parse','HEAD'],cwd,out/label/'head',env).strip()
        assert actual == sha
        assert run(['git','merge-base',VARIANTS['after'],MAIN],cwd,out/label/'merge-base',env).strip() == VARIANTS['before']
        configs[label] = [(cwd/p).read_bytes() for p in ['lean-toolchain','lakefile.toml','lake-manifest.json']]
        for p in ['lean-toolchain','lakefile.toml','lake-manifest.json']:
            d=out/label/p
            d.write_bytes((cwd/p).read_bytes())
        for name, count in CLIENTS.items():
            p = ROOT+name+'.lean'
            source=(cwd/p).read_bytes()
            if name == 'OrdinaryRing' and label == 'before':
                # Baseline has aggregate ring checks, not the head's 16 row certificates.
                assert 'private theorem row_' not in source.decode()
                assert 'by decide +kernel' in source.decode()
            else:
                certificates(source.decode(),count)
            sources[label,name]=hashlib.sha256(source).hexdigest()
            (out/label/(name+'.lean')).write_bytes(source)
        run(['scripts/cache/ensure.sh'],cwd,out/label/'bootstrap',env,1800)
        run(['lake','build','--wfail','--iofail',*[ (ROOT+n).replace('/','.') for n in CLIENTS]],
            cwd,out/label/'build',env,3600)
        flags[label]=[f'-D{k}={str(v).lower()}' for k,v in flatten(tomllib.loads((cwd/'lakefile.toml').read_text())['leanOptions'])]
        for name in CLIENTS:
            d=out/label/('setup-'+name)
            s=run(['lake','setup-file',ROOT+name+'.lean'],cwd,d,env)
            json.loads(s)
            setups[label,name]=d/'stdout'
    assert configs['before'] == configs['after'], 'toolchain/dependency/options mismatch'
    rows=[]
    for rep in range(4):
        for label in (list(VARIANTS) if rep%2==0 else list(reversed(VARIANTS))):
            cwd=workspace/f'source-{label}'
            for name in CLIENTS:
                p=ROOT+name+'.lean'
                assert hashlib.sha256((cwd/p).read_bytes()).hexdigest()==sources[label,name]
                d=out/f'{name}-{label}-{rep}'
                # GNU time includes descendants (maximum, not simultaneous sum).
                cmd=['/usr/bin/time','-v','-o',str(d/'time.txt'), 'lake','env','lean',
                     '--setup',str(setups[label,name]),*flags[label],
                     '-o',str(d/'result.olean'),'-i',str(d/'result.ilean'),p]
                run(cmd,cwd,d,envs[label])
                raw=(d/'time.txt').read_text()
                rss=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',raw)[1])
                rows.append(dict(module=name,variant=label,sha=VARIANTS[label],repetition=rep,
                                 warmup=rep==0,peak_rss_kib=rss,source_sha256=sources[label,name],
                                 evidence=str(d)))
                (out/'samples.json').write_text(json.dumps(rows,indent=2))
    (out/'complete.json').write_text(json.dumps(dict(samples=len(rows),verdict='none; manual interpretation required')))

if __name__ == '__main__':
    main()
