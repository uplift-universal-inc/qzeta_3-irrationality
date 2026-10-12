import QZeta3.DenominatorSieve
import QZeta3.DenominatorDescent
import QZeta3.CyclotomicPoleBounds
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Cyclotomic denominator clearing and a sufficient growth estimate

`denominators_clear` retains the original Proposition 4.1 / Appendix A
integrality statement, with the same cyclotomic exponents `cApp`.

The formal proof uses the elementary finite-sieve bound `107/192 < 11/18`
instead of formalizing the manuscript's sharper `321/(64π²)` asymptotic.
The public growth theorem is named `log_CK_sieve_le` to make that change
explicit; neither sharper growth assertion is retained as an unproved axiom.
-/

open Polynomial Finset Real

namespace QZeta3

variable {p : ℕ}

/-- **Proposition 4.1 (integrality).**  `C_K Δ_K ∈ ℤ[1/p][X]`. -/
theorem denominators_clear (hp : 2 ≤ p) (K i : ℕ) :
    ∃ m : ℕ, ((CK p K : ℚ) * (Delta p K).coeff i * (p : ℚ) ^ m).den = 1 := by
  exact Generic.denominators_clear_of_cyclotomic_bounds (𝕜 := ℂ) hp K i
    (Generic.cyclotomic_Delta_coeff_bound K i)

/-- The sufficient growth estimate used by the formal irrationality proof.
The manuscript's sharper π-based constant is not claimed here. -/
theorem log_CK_sieve_le (hp : 2 ≤ p) :
    ∃ c : ℝ, ∀ K : ℕ, 2 ≤ K →
      Real.log (CK p K : ℝ) ≤
        107 / 192 * (K : ℝ) ^ 3 * Real.log p + c * (K : ℝ) ^ 2 * Real.log K :=
  log_CK_rational_le hp

end QZeta3
