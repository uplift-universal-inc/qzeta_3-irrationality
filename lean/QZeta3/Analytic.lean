import QZeta3.AnalyticEntry

/-!
# The real functional and the real determinant bound (Proposition 2.1)

**Status:** the pure-pole identity, determinant bridge, and real determinant
bound are proved.

* `theta`, `Lfun` : `θ = x d/dx` and the functional `L(f) = ∑_{m ≥ 1} (θ²f)(q^m)`, `q = 1/p`
  (eq. (1.2)).
* `DK` : `D_K(x) = ∏_{a=1}^K (1 − q^a x)` (eq. (1.3)) as a real function.
* `gramR` : the real Gram matrix `[L(x^{i+j}/D_K)]`.
* `purity` (Lemma 1.2): `L((1 − q^a x)⁻¹) = ξ_p − S_a`.
* `gram_det_eq` : `det gramR = Δ_K(ξ_p)` — Lemma 1.2 plus the polynomial-division / partial-fraction
  bookkeeping of §3 (this is `QZeta3.Delta` evaluated at `ξ_p`).
* `gram_det_le` : the bound of Proposition 2.1 for the real Gram determinant.

Proposition 2.1 itself is stated in `QZeta3.Frozen.Prop21` and follows from `gram_det_eq` and
`gram_det_le`.

## Proof route (manuscript §2)

Replace `1, x, …, x^{K−1}` by the triple-root basis `B_j(x) = ∏_{t=1}^{j} (x − q^{⌈t/3⌉})`
(unipotent change of basis, determinant unchanged).  For nodes `q^m` with `m < ⌈j/3⌉` the jets of
`B_j` of order `≤ 2` vanish; at the remaining nodes `|θ^u B_j(q^m)| ≤ j^u q^{a_j} q^{m − ⌈j/3⌉}`.
Together with the uniform bounds `|W_K| ≤ e^{2/3}`, `|θ W_K| ≤ (4/3) e^{2/3} x`,
`|θ² W_K| ≤ (8/3) e^{2/3} x` for `W_K = 1/D_K` this gives
`|L(B_i B_j W_K)| ≤ 12 (i+j+1)² q^{a_i + a_j}`; extracting the row and column factors and applying
`Matrix.det_le` (the `K!` version of Hadamard's inequality available in Mathlib) gives the bound.

## Deviation from the manuscript

The manuscript's prefactor is `[12(2K−1)²√K]^K` (Hadamard).  Mathlib has `Matrix.det_le`
(`|det A| ≤ n! xⁿ` for entrywise bounds), which gives `K! (12(2K−1)²)^K`; both are
`exp(O(K log K))` and the assembly only needs that.
-/

open Polynomial Finset Filter Topology

namespace QZeta3

variable {p : ℕ}

/-- The real determinant bound in the triple-root basis (§2, eq. (2.2)–(2.6) and
`Matrix.det_le`). -/
theorem gram_det_le (hp : 2 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    |(gramR p K).det| ≤
      (K.factorial : ℝ) * (12 * (2 * (K : ℝ) - 1) ^ 2) ^ K * ((p : ℝ)⁻¹) ^ bK K := by
  exact gram_det_le_proved hp K

end QZeta3
