import QZeta3.Analytic

/-!
# Proposition 2.1 — the all-size real determinant bound (frozen statement)

Manuscript: Proposition 2.1 (`prop:analytic`).  For `q = 1/p ≤ 1/2` and `K ≥ 1`,

  `|Δ_K(ξ_p)| ≤ [12(2K−1)²√K]^K q^{b_K}`,  `b_K = (K³ + 3K² − c_{K mod 3})/9`.

## How to read the formal statement

* `DeltaR p K (xi p)` is `Δ_K(X)` evaluated at `X = ξ_p` (`QZeta3.Delta`, `QZeta3.xi`).
* `bK K = 2 ∑_{j<K} a_j` with `a_j = ∑_{t ≤ j} ⌈t/3⌉` (`QZeta3.aj`, `QZeta3.bK`); the closed
  form `(K³ + 3K² − c)/9` of the manuscript is not used, only `9 b_K ≥ K³ − K` (`QZeta3.bK_ge`).
* **Deviation.**  The prefactor is `K! · (12(2K−1)²)^K` instead of `[12(2K−1)²√K]^K`: Mathlib's
  `Matrix.det_le` is the `n! xⁿ` form of Hadamard's inequality.  Both are `exp(O(K log K))`,
  which is all §6 needs.

Status: proved from the kernel-checked `gram_det_eq` and `gram_det_le`
(see `QZeta3.Analytic`).
-/

namespace QZeta3

variable {p : ℕ}

/-- **Proposition 2.1.** `|Δ_K(ξ_p)| ≤ K! · (12(2K−1)²)^K · p^{−b_K}` for `p ≥ 2`, `K ≥ 1`. -/
theorem analytic_bound (hp : 2 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    |DeltaR p K (xi p)| ≤
      (K.factorial : ℝ) * (12 * (2 * (K : ℝ) - 1) ^ 2) ^ K * ((p : ℝ)⁻¹) ^ bK K := by
  rw [← gram_det_eq hp K]
  exact gram_det_le hp K hK

end QZeta3
