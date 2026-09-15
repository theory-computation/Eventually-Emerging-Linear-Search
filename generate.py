"""Regenerate and check the certificates for the fixed EA and FI lower bounds."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from importlib.util import find_spec
import os
import subprocess
import sys

sys.dont_write_bytecode = True
from verify import ROOT, check_sources, class_jobs, verify_one


def generate_one(job):
    ratio, index = job
    path = ROOT / 'proofs' / ratio.lower() / f'class{index}.json'
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        verify_one(path, ratio, index)
        return
    temporary = path.with_suffix('.json.tmp')
    try:
        result = subprocess.run(
            [sys.executable, '-B', str(ROOT / 'code/exact_producer.py'),
             '--ratio', ratio, '--class-index', str(index), '--out', str(temporary)],
            capture_output=True, text=True,
        )
        if result.returncode:
            raise ValueError(f'{ratio} class {index}: {result.stderr.strip()}')
        verify_one(temporary, ratio, index)
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, default=min(4, os.cpu_count() or 1))
    args = parser.parse_args()
    if args.workers < 1:
        parser.error('--workers must be positive')
    check_sources()
    for package in ('numpy', 'scipy', 'sympy'):
        if find_spec(package) is None:
            raise ValueError(f'Missing {package}; see README.md')
    for name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
        os.environ[name] = '1'
    pool = ThreadPoolExecutor(args.workers)
    try:
        for n, _ in enumerate(pool.map(generate_one, class_jobs()), 1):
            print(f'Generated or rechecked {n}/4848', flush=True)
    finally:
        pool.shutdown(wait=True, cancel_futures=True)
    print('Generation complete. Run python verify.py for the full coverage check.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError) as error:
        sys.exit(f'FAIL: {error}')
