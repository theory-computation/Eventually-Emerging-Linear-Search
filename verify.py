"""Verify every regenerated EA and FI certificate using the frozen verifier."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
EXPECTED = {
    'EA': (2400, 'bc8f71b69fdade02041a5c01fb899cb8205ed957b4861ef43e0de75546d6e557'),
    'FI': (2448, 'ae0ce1dd24fb5ea95130c0a09cbfbac73757673710f14ee2a7a56169dc080a22'),
}


def check_sources():
    for line in (ROOT / 'SOURCE_SHA256.txt').read_text().splitlines():
        digest, name = line.split()
        if sha256((ROOT / name).read_bytes()).hexdigest() != digest:
            raise ValueError(f'Source checksum mismatch: {name}')


def class_jobs():
    sys.path.insert(0, str(ROOT / 'code'))
    from independent_verifier import CASES, DEPTH, first_hit_reps
    if DEPTH != 7:
        raise ValueError('Expected depth seven')
    jobs = []
    for ratio, (count, digest) in EXPECTED.items():
        C, X = CASES[ratio]
        orders = [','.join(e.name for e in seq) + '\n' for seq in first_hit_reps(X, C)]
        if len(orders) != count or sha256(''.join(orders).encode()).hexdigest() != digest:
            raise ValueError(f'{ratio}: first-visitation universe mismatch')
        jobs.extend((ratio, i) for i in range(count))
    return jobs


def verify_one(path, ratio, index):
    if path.is_symlink() or not path.is_file():
        raise ValueError(f'{path}: expected a regular proof file')
    raw = path.read_bytes()
    proof = json.loads(raw)
    if proof.get('ratio') != ratio or type(proof.get('class_index')) is not int or proof['class_index'] != index:
        raise ValueError(f'{path}: wrong ratio or class')
    if proof.get('result', {}).get('reason') not in ('base', 'one-side'):
        raise ValueError(f'{path}: expected base or one-side closure')
    result = subprocess.run(
        [sys.executable, '-S', '-B', str(ROOT / 'code/independent_verifier.py'), str(path)],
        capture_output=True, text=True,
    )
    if result.returncode:
        raise ValueError(f'{path}: {result.stderr.strip() or result.stdout.strip()}')
    report, marker = result.stdout.strip().rsplit('\n', 1)
    report = json.loads(report)
    digest = sha256(raw).hexdigest()
    if (marker != 'INDEPENDENT_CLASS_VERIFIER=PASS' or report.get('status') != 'PASS'
            or report.get('ratio') != ratio or report.get('class_index') != index
            or report.get('proof_sha256') != digest
            or report.get('result', {}).get('reason') not in ('base', 'one-side')):
        raise ValueError(f'{path}: verifier result mismatch')
    return digest


def check_files():
    for ratio, (count, _) in EXPECTED.items():
        folder = ROOT / 'proofs' / ratio.lower()
        expected = {f'class{i}.json' for i in range(count)}
        if folder.is_symlink() or not folder.is_dir() or {p.name for p in folder.iterdir()} != expected:
            raise ValueError(f'{ratio}: expected exactly {count} proof files; run python generate.py first')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, default=min(4, os.cpu_count() or 1))
    args = parser.parse_args()
    if args.workers < 1:
        parser.error('--workers must be positive')
    check_sources()
    jobs = class_jobs()
    check_files()
    paths = [ROOT / 'proofs' / ratio.lower() / f'class{i}.json' for ratio, i in jobs]
    pool = ThreadPoolExecutor(args.workers)
    digests = []
    try:
        for n, digest in enumerate(pool.map(verify_one, paths, *zip(*jobs)), 1):
            digests.append(digest)
            if n % 100 == 0:
                print(f'Checked {n}/4848', flush=True)
    finally:
        pool.shutdown(wait=True, cancel_futures=True)
    check_files()
    for path, digest in zip(paths, digests):
        if path.is_symlink() or not path.is_file() or sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f'{path}: proof changed during verification')
    print('EA: 2400/2400 verified; lower bound 87/20 = 4.35')
    print('FI: 2448/2448 verified; lower bound 219/50 = 4.38')
    print('No combined-exhaustion closure used. ALL CERTIFICATES VERIFIED.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError) as error:
        sys.exit(f'FAIL: {error}')
