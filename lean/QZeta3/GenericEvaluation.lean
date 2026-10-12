import QZeta3.GenericSpecialization
import QZeta3.LocalEvaluation

open Polynomial Finset

namespace QZeta3.Generic

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

theorem natCast_pow_ne_one {p n : ℕ} (hp : 2 ≤ p) (hn : 0 < n) :
    (p : 𝕜)^n ≠ 1 := by
  have hpn : 1 < p^n := Nat.one_lt_pow (by omega : n ≠ 0) (by omega : 1 < p)
  intro h
  have he : p^n=1 := by exact_mod_cast h
  omega

theorem localizationData_natCast {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    LocalizationData (regularAt (p : 𝕜)) (RatFunc.X : RatFunc 𝕜) K := by
  refine ⟨base_mem_regularAt _, inv_base_mem_regularAt _ ?_, ?_⟩
  · exact_mod_cast (show p ≠ 0 by omega)
  · intro n hn
    exact inv_geometric_mem_regularAt _ n (natCast_pow_ne_one hp (mem_Icc.mp hn).1)

theorem Delta_coeff_mem_regularAt_natCast {p : ℕ} (hp : 2 ≤ p) (K i : ℕ) :
    (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i ∈ regularAt (p : 𝕜) :=
  (localizationData_natCast hp K).Delta_coeff_mem i

/-- Evaluating the generic moving-denominator determinant at an integer base
recovers exactly the rational determinant used in the irrationality argument. -/
theorem eval_Delta_coeff_natCast {p : ℕ} (hp : 2 ≤ p) (K i : ℕ) :
    RatFunc.eval (RingHom.id 𝕜) (p : 𝕜) ((Delta (RatFunc.X : RatFunc 𝕜) K).coeff i) =
      ((QZeta3.Delta p K).coeff i : 𝕜) := by
  have he := Specialization.specialize_Delta_coeff
    (localizationData_natCast (𝕜 := 𝕜) hp K) (localEval (p : 𝕜)) i
  simp only [localEval_apply, RatFunc.eval_X] at he
  rw [he]
  have hm := congrArg (fun f : 𝕜[X] => f.coeff i)
    (Specialization.map_Delta (Rat.castHom 𝕜) (p : ℚ) K)
  simpa only [Polynomial.coeff_map, Rat.coe_castHom, Rat.cast_natCast, Delta_natCast] using hm.symm

end QZeta3.Generic
