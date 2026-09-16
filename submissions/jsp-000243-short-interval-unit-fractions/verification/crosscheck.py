#!/usr/bin/env python3
"""Independent cross-check of the JSP-000243 answer.

Uses only exact rational arithmetic (``fractions.Fraction``), so it shares no
code and no reasoning path with the Lean proof.  It re-derives the three facts
that ``Proof.lean`` / ``Challenge.lean`` prove in the kernel:

  1. {2, 3, 6} is a subset of [2, 6] whose reciprocals sum to 1   (width 4);
  2. among all 32 subsets of {2,...,6} it is the ONLY one;
  3. for every a in 2..LIMIT, no subset of {a, a+1, a+2, a+3} sums to 1
     (so no interval of width <= 3 works).

Run:  python3 verification/crosscheck.py
"""
from fractions import Fraction
from itertools import combinations

LIMIT = 3000  # start points a to scan for width <= 3


def subsets(xs):
    for r in range(len(xs) + 1):
        yield from combinations(xs, r)


def sums_to_one(xs):
    return [S for S in subsets(xs) if sum((Fraction(1, k) for k in S), Fraction(0)) == 1]


def main() -> None:
    # (1) and (2): the width-4 interval [2, 6]
    winners = sums_to_one(list(range(2, 7)))
    print("subsets of {2,3,4,5,6} with reciprocal sum 1:", winners)
    assert winners == [(2, 3, 6)], winners

    # (3): no width <= 3 interval works, for any start a >= 2
    violations = []
    for a in range(2, LIMIT + 1):
        for S in subsets(list(range(a, a + 4))):
            if S and sum((Fraction(1, k) for k in S), Fraction(0)) == 1:
                violations.append((a, S))
    print("width<=3 violations for a in 2..%d: %d" % (LIMIT, len(violations)))
    assert not violations, violations[:5]

    print("OK: width 4 via [2,6] with {2,3,6}; unique; no width<=3 example.")


if __name__ == "__main__":
    main()
