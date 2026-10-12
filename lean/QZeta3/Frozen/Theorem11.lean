import QZeta3.Main

/-!
# Theorem 1.1 — the main theorem (frozen statement)

Manuscript: Theorem 1.1 (`thm:main`, "candidate main theorem"): for every integer `p ≥ 2` the
real number `ξ_p = ∑_{n ≥ 1} n²/(pⁿ − 1)` is irrational.

## How to read the formal statement

* `p : ℕ` with `2 ≤ p`.
* `xi p` is the `tsum` `∑' n : ℕ, (n+1)²/(p^{n+1} − 1)` (`QZeta3.xi`), which is the convergent
  series of the manuscript: `QZeta3.hasSum_xi` (proved) shows the series converges to `xi p`, so
  no "non-summable `tsum` is `0`" junk value is involved; `QZeta3.xi_pos` (proved) is a sanity
  check.  The indexing `n + 1` avoids the `n = 0` term `0/0`.
* `Irrational` is Mathlib's `x ∉ Set.range (Rat.cast)`.

A Mathlib-only restatement with every object rebuilt from Mathlib is in
`QZeta3Audit/Challenge.lean`, proved from this theorem in `QZeta3Audit/Solution.lean`
(leanprover/comparator configuration `QZeta3Audit/comparator.json`).

Status: proved from the kernel-checked analytic, content, cyclotomic denominator,
growth, and nonvanishing results. The growth estimate uses the sufficient rational
constant `107/192`; the theorem statement is unchanged.
-/

namespace QZeta3

/-- **Theorem 1.1.**  `∑_{n ≥ 1} n²/(pⁿ − 1)` is irrational for every integer `p ≥ 2`. -/
theorem theorem11 (p : ℕ) (hp : 2 ≤ p) : Irrational (xi p) :=
  irrational_xi hp

end QZeta3
