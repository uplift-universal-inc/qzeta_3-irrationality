import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Comparator challenge: the main theorem, stated from Mathlib alone

The statement of Theorem 1.1 of the manuscript *A moving-denominator Hankel argument for the
irrationality of ζ_{1/p}(3)* (11 October 2026), written with Mathlib's `Irrational` and `tsum`
only, in the style of the Formal Conjectures repository.  Read this file to see what is claimed.

English version: for every integer `p ≥ 2`, the real number `∑_{n ≥ 1} n²/(pⁿ − 1)` is
irrational.

The `tsum` is over `n : ℕ` with the summand written at `n + 1`, so the `n = 0` term `0/0` never
occurs; the series converges (see `QZeta3.summable_term` in the library), so the `tsum` is the
genuine sum.

This file contains the single intentional statement-level `sorry`, filled by `Solution.lean`.
-/

namespace QZeta3Challenge

/-- For every integer `p ≥ 2`, `∑_{n ≥ 1} n²/(pⁿ − 1)` is irrational. -/
theorem irrational_qzeta3 (p : ℕ) (hp : 2 ≤ p) :
    Irrational (∑' n : ℕ, ((n : ℝ) + 1) ^ 2 / ((p : ℝ) ^ (n + 1) - 1)) := by
  sorry

end QZeta3Challenge
