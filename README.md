# Eventually Emerging Linear Search

This repository regenerates and verifies the computer-assisted unconditional
two-agent lower bounds EA >= 87/20 = 4.35 and FI >= 219/50 = 4.38.
The finite necessary-condition argument is given in the paper cited below.

The four files in `code/` are the unchanged scientific sources used for these
bounds. Their SHA-256 checksums are recorded in `SOURCE_SHA256.txt`.

| File | Purpose |
| --- | --- |
| `exact_model.py` | Rational LP constraints and first-visitation orders. |
| `farkas_core.py` | Discover and reconstruct exact rational Farkas certificates. |
| `exact_producer.py` | Generate a certificate tree for one visitation order. |
| `independent_verifier.py` | Independently reconstruct the constraints and check the certificate tree. |

Both constructions use depth 7 and the following fixed checkpoint distances.
These values are already stored as exact fractions in the producer and verifier;
no additional input file is needed.

```text
EA: C = 87/20
X = (1, 7719/1000, 15969/1000, 3829/200, 6147/250,
     32707/1000, 24283/500, 27197/500, 136059/1000)

FI: C = 219/50
X = (1, 1241/200, 10693/1000, 541/40, 3103/200,
     4091/200, 28219/1000, 6871/125, 7928/125)
```

There are 2,400 remaining EA first-visitation orders and 2,448 FI orders.
The scripts regenerate these universes and check their ordered-list checksums.
Every order, including FI class 1165, must be verified.

Use Python 3.11 or 3.12. Generation requires NumPy, SciPy and SymPy. The original
computations used Python 3.11.5 and these package versions:

```text
python -m pip install numpy==1.26.4 scipy==1.13.1 sympy==1.12.1
```

SciPy supplies the HiGHS solver; no separate solver executable or commercial
solver is needed. SymPy's dependencies are installed automatically.
Verification requires only Python's standard library.

From this directory, run:

```text
python generate.py
python verify.py
```

Generation writes the proof files to `proofs/ea/` and `proofs/fi/`. Each file
contains rational Farkas multipliers and the branches they exclude. Numerical
optimization finds candidate multipliers; exact arithmetic checks nonnegativity,
zero combined left-hand side, and strictly negative combined right-hand side.
Floating-point infeasibility alone is never accepted as proof.

Each generated file is independently verified before being saved. Rerunning
generation rechecks completed files and continues with the missing classes.
An invalid existing file causes an error. Both commands use up to four workers;
append `--workers 1` or another positive number to change this.

Successful full verification ends with:

```text
EA: 2400/2400 verified; lower bound 87/20 = 4.35
FI: 2448/2448 verified; lower bound 219/50 = 4.38
No combined-exhaustion closure used. ALL CERTIFICATES VERIFIED.
```

The verifier checks every proof afresh and rejects missing, extra, invalid or
mislabelled files. The wrapper permits only base or one-side closure, matching
the promoted proofs. It does not accept combined-exhaustion closure.

Generation may take substantial time and can run on an ordinary multicore
machine. The original work used independent single-CPU tasks. One recorded
FI class, 1165, took 7438.425259 seconds to generate with a 4 GB memory allocation;
this is a single-class observation, not a full-run estimate. The original proof
collection occupied 3.6 GB. Verification avoids optimization and was much faster
in our small regeneration tests. We have no measured full regeneration or
verification time for one machine.

Package checks reproduced the complete visitation universes and regenerated and
verified EA classes 0 and 58 and FI class 0. The full 4,848-class computation was
not rerun while preparing this package.

Citation: [Authors, *Eventually Emerging Linear Search*, venue, year, DOI/arXiv
identifier to be added.]
