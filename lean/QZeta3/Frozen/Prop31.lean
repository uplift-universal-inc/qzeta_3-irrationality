import QZeta3.Leading
import QZeta3.ContentTruncation

/-!
# Proposition 3.1 — the coefficientwise factor at primes dividing `p` (frozen statement)

Manuscript: Proposition 3.1 (`prop:content`).  For every prime `ℓ ∣ p` with `r = v_ℓ(p)`, every
coefficient of `Δ_K(X)` has `ℓ`-adic valuation at least `r e_K`, and
`[X^K] Δ_K = (−1)^{K(K−1)/2} p^{e_K}`; in particular `deg Δ_K = K` and
`p^{−e_K} Δ_K ∈ ℤ_ℓ[X]` for every `ℓ ∣ p`.

## How to read the formal statements

* `content_coeff`: for every `i`, the rational number `(coeff Δ_K i) / p^{e_K}` has a denominator
  coprime to `p`.  This is exactly "`ℓ`-integral for every prime `ℓ ∣ p`", i.e. the valuation
  statement with multiplicity `v_ℓ(p) e_K` (a denominator coprime to `p` has no factor `ℓ`).
* `leading_coeff`: the coefficient of `X^K` is `(−1)^{K(K−1)/2} p^{e_K}` (`e_K = A_K (K−1)`,
  `QZeta3.eK`).  `K(K−1)/2` is natural-number division (exact).
* `natDegree_Delta`: `deg Δ_K = K`, derived; the main theorem only needs `deg Δ_K ≤ K`
  (`QZeta3.natDegree_Delta_le`, proved).

Status: `leading_coeff` is proved in `QZeta3.Leading`; `content_coeff` is proved
in `QZeta3.ContentTruncation`. The degree equality follows from these results.
-/

open Polynomial

namespace QZeta3

variable {p : ℕ}

/-- **Proposition 3.1 (content).**  `p^{−e_K} Δ_K` is integral at every prime dividing `p`. -/
theorem content_coeff (hp : 2 ≤ p) (K i : ℕ) :
    Nat.Coprime ((Delta p K).coeff i / (p : ℚ) ^ eK K).den p := by
  exact content_coeff_proved hp K i

/-- **Proposition 3.1 (leading coefficient).**  `[X^K] Δ_K = (−1)^{K(K−1)/2} p^{e_K}`. -/
theorem leading_coeff (hp : 2 ≤ p) (K : ℕ) :
    (Delta p K).coeff K = (-1) ^ (K * (K - 1) / 2) * (p : ℚ) ^ eK K :=
  leading_coeff_proved hp K

/-- `deg Δ_K = K` exactly. -/
theorem natDegree_Delta (hp : 2 ≤ p) (K : ℕ) : (Delta p K).natDegree = K := by
  apply le_antisymm (natDegree_Delta_le p K)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [leading_coeff hp K]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hp0)

end QZeta3
