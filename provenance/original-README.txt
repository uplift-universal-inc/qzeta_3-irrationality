Q-ZETA(3): ALL-SIZE PROOF CANDIDATE
11 October 2026

Target: for each integer p >= 2, sum_{n>=1} n^2/(p^n-1) is irrational.

STATUS
The enclosed manuscript assembles an unconditional mathematical argument for
the target. It is a research proof candidate that has passed internal,
separately derived checks. It has not been formally verified, externally
reviewed, or established as a published theorem. The finite computations are
consistency checks and do not substitute for any all-size argument.

MAIN PROOF
1. Pure q-Hermite moments identify a degree-K rational polynomial Delta_K.
2. A triple-root monic basis gives log|Delta_K(xi)| <= -(log p)K^3/9+O(K^2).
3. Local expansions prove coefficient content p^{K(K^2-1)/2} for the FULL
   determinant, including the polynomial quotient terms.
4. A corrected cyclotomic bound gives denominator exponent constant
   385/(64*pi^2) = 0.6095102453484382 < 11/18.
5. Moving-denominator rational interpolation proves infinitely many nonzero
   determinant values. This avoids an assumed sign pattern or congruence.
6. If xi=a/b, b^K times the normalized integer polynomial value would be a
   nonzero integer tending to zero along an infinite subsequence.

STRONGER VARIANT
A moving-node basis at paired cyclotomic collisions improves the denominator
constant to 321/(64*pi^2) = 0.5081890617061005. This variant is also internally
audited, but the conservative bound above already suffices.

CORRECTIONS TO EARLIER WORK
- The claim d>K/2 implies K-2<d is false. The missed polynomial moment j=d
  has rank <= max(0,K-d-1); the new proof charges for that rank explicitly.
- The purported modulo-3 sign rule is false at K=7 and K=9. It is not used.
- The original numerical zeta evaluator omitted the infinite tail enclosure.
  The audit evaluators add a proved, outward-rounded tail bound.
- A pure-pole content computation alone was insufficient. The new local
  moment expansion controls the entire determinant polynomial.
- Cubic-decay q-Hankel irrationality arguments have prior literature:
  Zudilin (2016), https://doi.org/10.1007/s40993-016-0042-x.

CONTENTS
q_zeta3_proof_candidate_2026-10-11.pdf: self-contained manuscript.
q_zeta3_proof_candidate_2026-10-11.tex: editable manuscript source.
verification.json: summary and exact finite-check metadata.
work/: detailed proof notes, internal audits, verification scripts/results.
source/zeta7-port/qhankel.py: original user-supplied construction engine.

REPRODUCING CHECKS
Requires Python 3 and python-flint. From the extracted archive root:
    python3 work/verify_assembly.py
    python3 work/fresh_arithmetic/check.py
    python3 work/denominator_repair/verify.py
    python3 work/audit/fast_verify.py 60

The first script checks both conservative and stronger denominator multipliers
against exact rational determinant coefficients for 88 (p,K) cases. It also
checks 62,500 cluster-weight formulas. The independent arithmetic script checks
100 determinant cases, including composite p. Existing larger K=60 interval
certificate uses an explicit infinite-series tail bound.

Use the repaired audit evaluators rather than the original run_q numerical
entry point, whose missing tail enclosure is retained as source history.

BUILDING THE PDF
    pdflatex -interaction=nonstopmode q_zeta3_proof_candidate_2026-10-11.tex
Run twice to resolve references. Standard amsmath/amsthm/hyperref packages are
used. No computer calculation is logically needed for the manuscript proof.

SCOPE
The target is q-zeta at q=1/p. No assertion about ordinary zeta(7), zeta(5),
Catalan's constant, or higher odd q-zeta values follows from this manuscript.
