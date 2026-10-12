import QZeta3.LowCyclotomicBound
import QZeta3.HighOrderDeterminant

/-! The complete local cyclotomic pole estimate, in both order ranges. -/

open Polynomial Finset
namespace QZeta3.Generic

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The Appendix A exponent clears every determinant coefficient at every primitive root. -/
theorem cyclotomic_Delta_coeff_bound (K i d : ℕ) (hd : d ∈ Icc 1 K)
    (ω : 𝕜) (hω : IsPrimitiveRoot ω d) :
    uniformizer ω ^ cApp K d * (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i ∈ regularAt ω := by
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have hdK : d ≤ K := (mem_Icc.mp hd).2
  by_cases hlo : 2*d ≤ K
  · exact low_cyclotomic_bound hω hd0 hdK hlo i
  · exact high_Delta_scaled_coeff_mem hω hd0 hdK (by omega)
      (hω.ne_zero (by omega)) i

end QZeta3.Generic
