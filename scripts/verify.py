#!/usr/bin/env python3
"""Recompute exact-input MVC witnesses using outward Arb ball arithmetic.
This is a computer-assisted certificate verifier, NOT a Lean theorem-prover proof.
No numerical rootfinder or saved success flag is used.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import importlib.metadata
import json
from pathlib import Path
import sys
import time
from flint import acb, arb, acb_poly, fmpq, ctx

ROOT = Path(__file__).resolve().parents[1]
DEGREES = (2650, 2725, 2798, 2840, 2917)
TARGETS = {2650: Fraction(99964059, 10**8), 2725: Fraction(9996431, 10**7),
           2798: Fraction(999649, 10**6), 2840: Fraction(249917, 250000),
           2917: Fraction(1000000129, 10**9)}

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def rational_ball(x):
    return arb(fmpq(x.numerator, x.denominator))

def finite(values, label):
    require(all(v.is_finite() for v in values), f'Nonfinite {label}')

def read_centers(path):
    rows = json.loads(path.read_text())['centers']
    require(isinstance(rows, list), 'Centers must be a list')
    result = []
    for row in rows:
        require(isinstance(row, list) and len(row) == 2, 'Invalid complex pair')
        parts = []
        for part in row:
            require(isinstance(part, list) and len(part) == 2, 'Invalid rational pair')
            n, d = part
            require(type(n) is int and type(d) is int and d > 0, 'Invalid rational encoding')
            parts.append(Fraction(n, d))
        require(any(parts), 'Zero cannot be a normalized critical point')
        result.append(tuple(parts))
    return result

def verify(degree, bits=32000):
    require(degree in DEGREES, 'Unknown witness')
    require(bits >= 64, 'Precision must be at least 64 bits')
    start = time.time()
    ctx.prec = bits
    base = ROOT / 'witnesses' / str(degree)
    cfg = json.loads((base / 'config.json').read_text())
    source = base / 'critical_centers.json'
    require(cfg['degree'] == degree, 'Degree mismatch')
    require(sha(source) == cfg['critical_centers_sha256'], 'Exact input hash mismatch')
    target = Fraction(cfg['exact_target'])
    require(target == TARGETS[degree] and target > 0, 'Unexpected exact target')
    centers = read_centers(source)
    require(len(centers) == degree - 1, 'Incomplete critical multiset')
    roots = [acb(rational_ball(x), rational_ball(y)) for x, y in centers]
    finite(roots, 'critical centers')
    require(all(abs(c) > 0 for c in roots), 'Root ball contains zero')
    monic_q = acb_poly.from_roots(roots)
    finite(list(monic_q), 'derivative coefficients')
    require(monic_q.degree() == degree - 1, 'Derivative degree not certified')
    require(abs(monic_q[0]) > 0, 'Normalizing constant not separated from zero')
    # Exactly: P = integral(monic_q) / monic_q(0).
    # Consequently P(0)=0 and P'(0)=1 by polynomial identities.
    p = monic_q.integral() * (1 / monic_q[0])
    finite(list(p), 'primitive coefficients')
    require(p.degree() == degree, 'Primitive degree not certified')
    values = p.evaluate(roots, algorithm='fast')
    require(len(values) == degree - 1, 'Missing evaluations')
    finite(values, 'critical values')
    quotients = [v / c for v, c in zip(values, roots)]
    finite(quotients, 'critical quotients')
    magnitudes = [abs(v) for v in quotients]
    finite(magnitudes, 'critical quotient moduli')
    target_ball = rational_ball(target)
    require(all(x > target_ball for x in magnitudes), 'Strict target not certified at this precision')
    strings = [x.str(50) for x in magnitudes]
    exported = [arb(x) for x in strings]
    finite(exported, 'serialized intervals')
    require(all(x.contains(y) for x, y in zip(exported, magnitudes)), 'Serialization lost enclosure')
    require(all(x > target_ball for x in exported), 'Serialization lost strict inequality')
    return {'status': 'PASS', 'degree': degree, 'exact_target': str(target),
            'critical_count_with_multiplicity': len(centers), 'distinct_critical_count': len(Counter(centers)),
            'precision_bits': bits, 'all_intervals_finite': True,
            'all_ratio_intervals': strings, 'critical_centers_sha256': sha(source),
            'verifier_sha256': sha(Path(__file__)),
            'python_flint_version': importlib.metadata.version('python-flint'),
            'elapsed_seconds': time.time() - start}

def coverage():
    # These ranges follow only AFTER witness verification and the extension lemma.
    ranges = []
    for n in DEGREES:
        t = TARGETS[n]
        if t > 1:
            last = None
        else:
            inverse = 1 / (1 - t)
            last = (inverse.numerator - 1) // inverse.denominator
            require(t > Fraction(last - 1, last), 'Incorrect right endpoint')
            require(t <= Fraction(last, last + 1), 'Range is not maximal')
        ranges.append((n, last))
    covered = 2649
    for first, last in ranges:
        require(first <= covered + 1, 'Gap in degree coverage')
        if last is None:
            return {'strong_every_degree_at_least': 2650, 'ordinary_every_degree_at_least': 2917,
                    'ranges': ranges, 'proof': 'docs/DEGREE_EXTENSION.md',
                    'scope': 'Existence at each degree; not all polynomials; not global minimality.'}
        covered = max(covered, last)
    raise ValueError('Missing infinite tail')

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--degree', type=int, choices=DEGREES)
    ap.add_argument('--bits', type=int, default=32000)
    ap.add_argument('--output', type=Path, help='New directory for fresh full reports')
    args = ap.parse_args()
    degrees = (args.degree,) if args.degree else DEGREES
    if args.output:
        args.output.mkdir(parents=True, exist_ok=False)
    for degree in degrees:
        report = verify(degree, args.bits)
        if args.output:
            (args.output / f'{degree}.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps({k: v for k, v in report.items() if k != 'all_ratio_intervals'}), flush=True)
    if not args.degree:
        chain = coverage()
        print(json.dumps(chain), flush=True)
        if args.output:
            (args.output / 'coverage.json').write_text(json.dumps(chain, indent=2) + '\n')

if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError) as exc:
        print(f'FAIL: {exc}', file=sys.stderr)
        raise SystemExit(1)
