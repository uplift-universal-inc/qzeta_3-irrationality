import QZeta3.CyclotomicLocal

/-! # Exact upper-node cancellation in double cyclotomic clusters

The refined high-order denominator estimate uses a second basis vector which
vanishes at the moving upper node. Its other residue meets a regular tail and
therefore needs no cubic pole allowance.
-/

open Polynomial Finset

namespace QZeta3.Generic

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- A regular pole tail costs no additional uniformizer power. -/
theorem proper_term_coeff_mem_of_tail_regular (ω : 𝕜) (hω : ω ≠ 0)
    (K a : ℕ) (ha : a ∈ Icc 1 K) (N : RatFunc 𝕜) (v w : ℕ)
    (hN : N / uniformizer ω ^ v ∈ regularAt ω)
    (hS : S (RatFunc.X : RatFunc 𝕜) a ∈ regularAt ω)
    (hw : collisionCount ω K a ≤ w+v) (i : ℕ) :
    (C (uniformizer ω ^ w * (N /
        (RatFunc.X ^ a * (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X ^ a)))) *
      (X-C (S (RatFunc.X : RatFunc 𝕜) a))).coeff i ∈ regularAt ω := by
  let D : RatFunc 𝕜 := RatFunc.X ^ a *
    (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X ^ a)
  have hD : uniformizer ω ^ collisionCount ω K a / D ∈ regularAt ω := by
    have h := (regularAt ω).mul_mem (uniformizer_pow_div_derivative_mem ω hω K a ha)
      ((regularAt ω).pow_mem (inv_base_mem_regularAt ω hω) a)
    convert h using 1
    simp only [D, div_eq_mul_inv, mul_inv, inv_pow]
    ring
  have hscalar := scaled_ratio_mem ω N D v (collisionCount ω K a) w hN hD hw
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub]
  by_cases hi0 : i = 0
  · subst i
    simpa only [Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, mul_neg]
      using (regularAt ω).neg_mem ((regularAt ω).mul_mem hscalar hS)
  · by_cases hi1 : i = 1
    · subst i
      simpa using hscalar
    · simp [Polynomial.coeff_X, Polynomial.coeff_C, hi0, Ne.symm hi1]

/-- The upper-node factor contributes one uniformizer at the lower node. -/
theorem shifted_cluster_numerator_eval_div_mem (ω : 𝕜) (a b j : ℕ)
    (hab : ω ^ a = ω ^ b) (V : (RatFunc 𝕜)[X])
    (hV : ∀ i, V.coeff i ∈ regularAt ω) :
    ((V * (X-C (RatFunc.X ^ b)) ^ j).eval (RatFunc.X ^ a)) /
      uniformizer ω ^ j ∈ regularAt ω := by
  have hv := eval_mem_regularAt ω V hV (RatFunc.X ^ a)
    ((regularAt ω).pow_mem (base_mem_regularAt ω) a)
  have hd := difference_div_uniformizer_mem ω a b hab
  have h := (regularAt ω).mul_mem hv ((regularAt ω).pow_mem hd j)
  convert h using 1
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, div_pow]
  ring

/-- At the upper node the shifted basis polynomial vanishes exactly. -/
theorem shifted_cluster_eval_upper (b j : ℕ) (hj : 0 < j) (V : (RatFunc 𝕜)[X]) :
    (V * (X-C (RatFunc.X ^ b)) ^ j).eval (RatFunc.X ^ b) = 0 := by
  simp [Nat.ne_zero_of_lt hj]

/-- Every mixed or second-row proper entry in the refined double cluster is regular. -/
theorem double_cluster_lower_proper_regular (ω : 𝕜) (hω : ω ≠ 0)
    (K a b j k : ℕ) (ha : a ∈ Icc 1 K) (hab : ω ^ a = ω ^ b)
    (hc : collisionCount ω K a ≤ 1) (hjk : 0 < j+k)
    (hS : S (RatFunc.X : RatFunc 𝕜) a ∈ regularAt ω)
    (V : (RatFunc 𝕜)[X]) (hV : ∀ i, V.coeff i ∈ regularAt ω) (i : ℕ) :
    (C (((V * (X-C (RatFunc.X ^ b)) ^ j).eval (RatFunc.X ^ a) *
          (V * (X-C (RatFunc.X ^ b)) ^ k).eval (RatFunc.X ^ a)) /
        (RatFunc.X ^ a * (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X ^ a))) *
      (X-C (S (RatFunc.X : RatFunc 𝕜) a))).coeff i ∈ regularAt ω := by
  have hN := product_div_uniformizer_pow_mem ω _ _ j k
    (shifted_cluster_numerator_eval_div_mem ω a b j hab V hV)
    (shifted_cluster_numerator_eval_div_mem ω a b k hab V hV)
  simpa using proper_term_coeff_mem_of_tail_regular ω hω K a ha _ (j+k) 0 hN hS (by omega) i

/-- The upper-node residue of every mixed or second-row entry is identically zero. -/
theorem double_cluster_upper_proper_zero (K b j k : ℕ) (hjk : 0 < j+k)
    (V : (RatFunc 𝕜)[X]) :
    C (((V * (X-C (RatFunc.X ^ b)) ^ j).eval (RatFunc.X ^ b) *
          (V * (X-C (RatFunc.X ^ b)) ^ k).eval (RatFunc.X ^ b)) /
        (RatFunc.X ^ b * (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X ^ b))) *
      (X-C (S (RatFunc.X : RatFunc 𝕜) b)) = 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hk : 0 < k := by omega
    rw [shifted_cluster_eval_upper b k hk V]
    simp
  · rw [shifted_cluster_eval_upper b j hj V]
    simp

end QZeta3.Generic
