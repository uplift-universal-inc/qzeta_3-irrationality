import QZeta3.ResidueDenominators

/-! # Finite truncation for the base-prime content argument

This module replaces the analytic local series in Proposition 3.1 by finite
polynomials and an explicitly controlled error. No p-adic convergence is needed.
-/

open Polynomial Finset

namespace QZeta3

variable {p : ℕ}

/-- Numerator of the tail of the square-weighted geometric series. -/
def squareTailNumerator (M : ℕ) (y : ℚ) : ℚ :=
  ((M : ℚ) + 1) ^ 2 + (1 - 2 * M - 2 * (M : ℚ) ^ 2) * y + (M : ℚ) ^ 2 * y ^ 2

/-- Exact finite identity for the second Euler derivative of a geometric series. -/
theorem square_geometric_finite (M : ℕ) (y : ℚ) :
    y * (1 + y) = (1 - y) ^ 3 * (∑ j ∈ range (M + 1), (j : ℚ) ^ 2 * y ^ j) +
      y ^ (M + 1) * squareTailNumerator M y := by
  induction M with
  | zero => simp [squareTailNumerator]
  | succ M ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    simp only [squareTailNumerator] at *
    push_cast
    rw [pow_succ y (M + 1)]
    ring

/-- The geometric generating function equals its finite truncation plus its exact tail. -/
theorem g_eq_finite_add_tail (M : ℕ) (y : ℚ) (hy : y ≠ 1) :
    g y = (∑ j ∈ range (M + 1), (j : ℚ) ^ 2 * y ^ j) +
      y ^ (M + 1) * (squareTailNumerator M y / (1 - y) ^ 3) := by
  unfold g
  have h1 : 1 - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  apply (div_eq_iff (pow_ne_zero 3 h1)).mpr
  have h := square_geometric_finite M y
  field_simp
  linear_combination h

/-- The tail numerator is an integer at integral arguments. -/
theorem squareTailNumerator_int (M : ℕ) (y : ℤ) :
    squareTailNumerator M (y : ℚ) =
      ((((M : ℤ) + 1) ^ 2 + (1 - 2 * M - 2 * (M : ℤ) ^ 2) * y +
        (M : ℤ) ^ 2 * y ^ 2 : ℤ) : ℚ) := by
  unfold squareTailNumerator
  push_cast
  rfl

/-- The quotient in the geometric tail is integral at every prime dividing the base. -/
theorem squareTail_mem_baseIntegral (hp : 2 ≤ p) (M b : ℕ) (hb : 0 < b) :
    squareTailNumerator M ((p : ℚ) ^ b) / (1 - (p : ℚ) ^ b) ^ 3 ∈ baseIntegral p := by
  have hpow : 1 ≤ p ^ b := one_le_pow₀ (show 1 ≤ p by omega)
  have hcast : (((p : ℤ) ^ b : ℤ) : ℚ) = (p : ℚ) ^ b := by norm_cast
  rw [← hcast, squareTailNumerator_int]
  have hcop : Nat.Coprime ((1 - (p : ℤ) ^ b) ^ 3).natAbs p := by
    rw [Int.natAbs_pow]
    apply Nat.Coprime.pow_left
    have heq : (1 - (p : ℤ) ^ b).natAbs = p ^ b - 1 := by
      rw [← Int.natAbs_neg]
      have hneg : -(1 - (p : ℤ) ^ b) = ((p ^ b - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_one]
        ring
      rw [hneg, Int.natAbs_natCast]
    rw [heq]
    exact pow_sub_one_coprime p b (by omega) hb
  convert intCast_div_mem_baseIntegral
    (((M : ℤ) + 1) ^ 2 + (1 - 2 * M - 2 * (M : ℤ) ^ 2) * (p : ℤ) ^ b +
      (M : ℤ) ^ 2 * ((p : ℤ) ^ b) ^ 2) ((1 - (p : ℤ) ^ b) ^ 3) hcop using 1
  push_cast
  rfl

/-- Truncating the series for `g(p^b)` after degree `M` leaves an error divisible
by `p^(M+1)` in the integral-at-the-base subring, uniformly in `b ≥ 1`. -/
theorem g_truncation_mem_baseIntegral (hp : 2 ≤ p) (M b : ℕ) (hb : 0 < b) :
    (g ((p : ℚ) ^ b) - ∑ j ∈ range (M + 1), (j : ℚ) ^ 2 * ((p : ℚ) ^ b) ^ j) /
      (p : ℚ) ^ (M + 1) ∈ baseIntegral p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hy : (p : ℚ) ^ b ≠ 1 := ne_of_gt
    (one_lt_pow₀ (by exact_mod_cast (show 1 < p by omega)) (Nat.ne_zero_of_lt hb))
  rw [g_eq_finite_add_tail M _ hy, add_sub_cancel_left]
  have he : b * (M + 1) = (M + 1) + (b - 1) * (M + 1) := by
    have : b = (b - 1) + 1 := by omega
    nlinarith
  rw [← pow_mul, he, pow_add, mul_assoc, mul_div_cancel_left₀ _ (pow_ne_zero _ hp0)]
  exact (baseIntegral p).mul_mem
    ((baseIntegral p).pow_mem (natCast_mem (baseIntegral p) p) _)
    (squareTail_mem_baseIntegral hp M b hb)

/-- Coefficients of the finite local translation polynomial. -/
def localCoeff (p j : ℕ) : ℚ := (j : ℚ) ^ 2 * (p : ℚ) ^ j / (1 - (p : ℚ) ^ j)

theorem localCoeff_mem_baseIntegral (hp : 2 ≤ p) (j : ℕ) :
    localCoeff p j ∈ baseIntegral p := by
  have heq : localCoeff p j = -(mu p j * (p : ℚ) ^ j) := by
    by_cases hj : j = 0
    · simp [localCoeff, mu, hj]
    · unfold localCoeff mu
      rw [ite_eq_right hj, show (1 : ℚ) - (p : ℚ) ^ j = -((p : ℚ) ^ j - 1) by ring, div_neg]
      ring
  rw [heq]
  exact (baseIntegral p).neg_mem ((baseIntegral p).mul_mem
    (mu_mem_baseIntegral p j (by omega))
    ((baseIntegral p).pow_mem (natCast_mem (baseIntegral p) p) j))

/-- Finite version of the local translation series in Proposition 3.1. -/
noncomputable def localTruncPolynomial (p M : ℕ) : ℚ[X] :=
  ∑ j ∈ range (M + 1), monomial j (localCoeff p j)

theorem localTruncPolynomial_coeff_mem (hp : 2 ≤ p) (M i : ℕ) :
    (localTruncPolynomial p M).coeff i ∈ baseIntegral p := by
  unfold localTruncPolynomial
  rw [Polynomial.finsetSum_coeff]
  apply (baseIntegral p).sum_mem
  intro j _
  simp only [Polynomial.coeff_monomial]
  split_ifs
  · exact localCoeff_mem_baseIntegral hp j
  · exact (baseIntegral p).zero_mem

theorem localTruncPolynomial_eval (p M : ℕ) (x : ℚ) :
    (localTruncPolynomial p M).eval x =
      ∑ j ∈ range (M + 1), localCoeff p j * x ^ j := by
  simp [localTruncPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- A single geometric summation step in the local translation polynomial. -/
theorem localCoeff_step (hp : 2 ≤ p) (a j : ℕ) :
    localCoeff p j * (((p : ℚ) ^ (a + 1)) ^ j - ((p : ℚ) ^ a) ^ j) =
      -(j : ℚ) ^ 2 * ((p : ℚ) ^ (a + 1)) ^ j := by
  by_cases hj : j = 0
  · simp [localCoeff, hj]
  have hne : (1 : ℚ) - (p : ℚ) ^ j ≠ 0 := by
    have hpow : (1 : ℚ) < (p : ℚ) ^ j :=
      one_lt_pow₀ (by exact_mod_cast (show 1 < p by omega)) hj
    linarith
  unfold localCoeff
  rw [pow_succ (p : ℚ) a, mul_pow]
  field_simp
  ring

/-- The finite polynomial reproduces the finite sum of truncated geometric series. -/
theorem localTruncPolynomial_difference (hp : 2 ≤ p) (M a : ℕ) :
    (localTruncPolynomial p M).eval ((p : ℚ) ^ a) -
      (localTruncPolynomial p M).eval 1 =
      -∑ b ∈ Icc 1 a, ∑ j ∈ range (M + 1), (j : ℚ) ^ 2 * ((p : ℚ) ^ b) ^ j := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hstep : (localTruncPolynomial p M).eval ((p : ℚ) ^ (a + 1)) -
        (localTruncPolynomial p M).eval ((p : ℚ) ^ a) =
        -∑ j ∈ range (M + 1), (j : ℚ) ^ 2 * ((p : ℚ) ^ (a + 1)) ^ j := by
      rw [localTruncPolynomial_eval, localTruncPolynomial_eval, ← Finset.sum_sub_distrib,
        ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_sub, localCoeff_step hp]
      ring
    rw [Finset.sum_Icc_succ_top (by omega)]
    linear_combination ih + hstep

/-- The rational pole-tail is minus the finite sum of the local generating function. -/
theorem S_eq_neg_sum_local_g (hp : 2 ≤ p) (a : ℕ) :
    S p a = -∑ b ∈ Icc 1 a, g ((p : ℚ) ^ b) := by
  rw [S_eq_sum_g hp, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  apply g_inv
  · exact pow_ne_zero b (by exact_mod_cast (show p ≠ 0 by omega))
  · exact ne_of_gt (one_lt_pow₀ (by exact_mod_cast (show 1 < p by omega))
      (by have := (Finset.mem_Icc.mp hb).1; omega))

/-- Finite arithmetic substitute for the p-adic identity `S_a = -Z + H(p^a)`.
The error is divisible by `p^(M+1)` in the rational local subring. -/
theorem S_truncation_mem_baseIntegral (hp : 2 ≤ p) (M a : ℕ) :
    (S p a - ((localTruncPolynomial p M).eval ((p : ℚ) ^ a) -
      (localTruncPolynomial p M).eval 1)) / (p : ℚ) ^ (M + 1) ∈ baseIntegral p := by
  rw [S_eq_neg_sum_local_g hp, localTruncPolynomial_difference hp]
  have heq : (-∑ b ∈ Icc 1 a, g ((p : ℚ) ^ b) -
        -∑ b ∈ Icc 1 a, ∑ j ∈ range (M + 1), (j : ℚ) ^ 2 * ((p : ℚ) ^ b) ^ j) /
        (p : ℚ) ^ (M + 1) =
      -∑ b ∈ Icc 1 a, (g ((p : ℚ) ^ b) -
        ∑ j ∈ range (M + 1), (j : ℚ) ^ 2 * ((p : ℚ) ^ b) ^ j) /
          (p : ℚ) ^ (M + 1) := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    ring
  rw [heq]
  apply (baseIntegral p).neg_mem
  apply (baseIntegral p).sum_mem
  intro b hb
  exact g_truncation_mem_baseIntegral hp M b (Finset.mem_Icc.mp hb).1

/-- Evaluation preserves base-integrality when both coefficients and argument are integral. -/
theorem eval_mem_baseIntegral (p : ℕ) (f : ℚ[X])
    (hf : ∀ i, f.coeff i ∈ baseIntegral p) (x : ℚ) (hx : x ∈ baseIntegral p) :
    f.eval x ∈ baseIntegral p := by
  rw [Polynomial.eval_eq_sum_range]
  exact (baseIntegral p).sum_mem fun i _ =>
    (baseIntegral p).mul_mem (hf i) ((baseIntegral p).pow_mem hx i)

theorem localTruncPolynomial_zero_coeff (p M : ℕ) :
    (localTruncPolynomial p M).coeff 0 = 0 := by
  simp [localTruncPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, localCoeff]

/-- The finite local translation polynomial is divisible by its variable. -/
theorem localTruncPolynomial_divX_eval (p M : ℕ) (x : ℚ) :
    (localTruncPolynomial p M).eval x =
      (localTruncPolynomial p M).divX.eval x * x := by
  have h := congrArg (Polynomial.eval x) (Polynomial.divX_mul_X_add (localTruncPolynomial p M))
  simpa [localTruncPolynomial_zero_coeff] using h.symm

/-- The polynomial part of the translated residue sum is integral for every moment index,
including zero. -/
theorem localTrunc_residue_mem (hp : 2 ≤ p) (K k M : ℕ) :
    (∑ a ∈ Icc 1 K, (res p K k a / (p : ℚ) ^ a) *
      (localTruncPolynomial p M).eval ((p : ℚ) ^ a)) ∈ baseIntegral p := by
  let f : ℚ[X] := X ^ k * (localTruncPolynomial p M).divX
  have hf : ∀ i, f.coeff i ∈ baseIntegral p := by
    intro i
    simp only [f, Polynomial.coeff_X_pow_mul', Polynomial.coeff_divX]
    split_ifs
    · exact localTruncPolynomial_coeff_mem hp M _
    · exact (baseIntegral p).zero_mem
  have hsum : (∑ a ∈ Icc 1 K, (res p K k a / (p : ℚ) ^ a) *
      (localTruncPolynomial p M).eval ((p : ℚ) ^ a)) =
      ∑ a ∈ Icc 1 K, f.eval ((p : ℚ) ^ a) /
        (derivative (F p K)).eval ((p : ℚ) ^ a) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [localTruncPolynomial_divX_eval]
    simp only [f, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, res, ← pow_mul]
    have hp0 : (p : ℚ) ^ a ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show p ≠ 0 by omega))
    field_simp
  rw [hsum]
  exact residue_sum_mem_baseIntegral hp K f hf

/-- The universal residue denominator bound absorbs the finite truncation error. -/
theorem localTrunc_error_residue_mem (hp : 2 ≤ p) (K k a : ℕ) (ha : a ∈ Icc 1 K) :
    (res p K k a / (p : ℚ) ^ a) *
      (S p a - ((localTruncPolynomial p (K*K+K)).eval ((p : ℚ) ^ a) -
        (localTruncPolynomial p (K*K+K)).eval 1)) ∈ baseIntegral p := by
  have h := (baseIntegral p).mul_mem
    ((baseIntegral p).mul_mem (residue_scaled_mem hp K k a ha)
      (S_truncation_mem_baseIntegral hp (K*K+K) a))
    (natCast_mem (baseIntegral p) p)
  convert h using 1
  rw [pow_succ]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  field_simp

/-- The constant moments become integral after subtracting the finite local
translation times their linear coefficient. This is the arithmetic heart of
Proposition 3.1, proved using a finite truncation rather than a convergent local series. -/
theorem mConst_sub_translation_mem (hp : 2 ≤ p) (K k : ℕ) :
    mConst p K k - (localTruncPolynomial p (K*K+K)).eval 1 * mLin p K k ∈
      baseIntegral p := by
  have hQ := quotient_moment_mem_baseIntegral p K k (show 1 ≤ p by omega)
  have hH := localTrunc_residue_mem hp K k (K*K+K)
  have hE : (∑ a ∈ Icc 1 K, (res p K k a / (p : ℚ) ^ a) *
      (S p a - ((localTruncPolynomial p (K*K+K)).eval ((p : ℚ) ^ a) -
        (localTruncPolynomial p (K*K+K)).eval 1))) ∈ baseIntegral p :=
    (baseIntegral p).sum_mem fun a ha => localTrunc_error_residue_mem hp K k a ha
  have h := (baseIntegral p).add_mem ((baseIntegral p).add_mem hQ hH) hE
  convert h using 1
  unfold mConst mLin
  rw [mul_neg, sub_neg_eq_add, Finset.mul_sum]
  simp only [add_assoc]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The exceptional linear moment loses exactly `p^A_K` and no more. -/
theorem scaled_mLin_zero (hp : 2 ≤ p) (K : ℕ) (hK : 0 < K) :
    (p : ℚ) ^ AK K * mLin p K 0 = (-1 : ℚ) ^ K := by
  have hp0 : (p : ℚ) ^ AK K ≠ 0 := pow_ne_zero _
    (by exact_mod_cast (show p ≠ 0 by omega))
  rw [mLin_zero hp K hK, F_eval_zero, mul_inv]
  have hs : (((-1 : ℚ) ^ K)⁻¹) = (-1 : ℚ) ^ K := by
    rw [← inv_pow]
    norm_num
  rw [hs, mul_left_comm, mul_inv_cancel₀ hp0, mul_one]

theorem mConst_mem_baseIntegral (hp : 2 ≤ p) (K k : ℕ) (hk : 0 < k) :
    mConst p K k ∈ baseIntegral p := by
  have hZ := eval_mem_baseIntegral p (localTruncPolynomial p (K*K+K))
    (localTruncPolynomial_coeff_mem hp (K*K+K)) 1 (baseIntegral p).one_mem
  have h := (baseIntegral p).add_mem (mConst_sub_translation_mem hp K k)
    ((baseIntegral p).mul_mem hZ (mLin_mem_baseIntegral hp K k hk))
  simpa only [sub_add_cancel] using h

theorem scaled_mConst_zero_mem (hp : 2 ≤ p) (K : ℕ) (hK : 0 < K) :
    (p : ℚ) ^ AK K * mConst p K 0 ∈ baseIntegral p := by
  have hZ := eval_mem_baseIntegral p (localTruncPolynomial p (K*K+K))
    (localTruncPolynomial_coeff_mem hp (K*K+K)) 1 (baseIntegral p).one_mem
  have hR := (baseIntegral p).mul_mem
    ((baseIntegral p).pow_mem (natCast_mem (baseIntegral p) p) (AK K))
    (mConst_sub_translation_mem hp K 0)
  have hL : (p : ℚ) ^ AK K * mLin p K 0 ∈ baseIntegral p := by
    rw [scaled_mLin_zero hp K hK]
    exact (baseIntegral p).pow_mem ((baseIntegral p).neg_mem (baseIntegral p).one_mem) K
  have h := (baseIntegral p).add_mem hR ((baseIntegral p).mul_mem hZ hL)
  convert h using 1
  ring

/-- Every coefficient of the matrix obtained by scaling the exceptional row is integral. -/
theorem contentMatrix_coeff_integral (hp : 2 ≤ p) (K : ℕ) (hK : 0 < K) :
    ∀ a b i, ((contentMatrix p K) a b).coeff i ∈ baseIntegral p := by
  intro a b i
  let s : ℚ := if a.val = 0 then (p : ℚ) ^ AK K else 1
  have hs : s ∈ baseIntegral p := by
    dsimp [s]
    split_ifs
    · exact (baseIntegral p).pow_mem (natCast_mem (baseIntegral p) p) _
    · exact (baseIntegral p).one_mem
  have hC : s * mConst p K (a.val + b.val) ∈ baseIntegral p := by
    by_cases hk : a.val + b.val = 0
    · have ha : a.val = 0 := by omega
      rw [hk]
      simpa only [s, ha, ite_true] using scaled_mConst_zero_mem hp K hK
    · exact (baseIntegral p).mul_mem hs (mConst_mem_baseIntegral hp K _ (Nat.pos_of_ne_zero hk))
  have hL : s * mLin p K (a.val + b.val) ∈ baseIntegral p := by
    by_cases hk : a.val + b.val = 0
    · have ha : a.val = 0 := by omega
      rw [hk]
      simp only [s, ha, ite_true, scaled_mLin_zero hp K hK]
      exact (baseIntegral p).pow_mem ((baseIntegral p).neg_mem (baseIntegral p).one_mem) K
    · exact (baseIntegral p).mul_mem hs (mLin_mem_baseIntegral hp K _ (Nat.pos_of_ne_zero hk))
  have heq : (contentMatrix p K) a b =
      C (s * mConst p K (a.val + b.val)) + C (s * mLin p K (a.val + b.val)) * X := by
    unfold contentMatrix momentMatrix
    dsimp [s]
    split_ifs <;> simp only [map_mul, one_mul] <;> ring
  rw [heq, Polynomial.coeff_add, Polynomial.coeff_C_mul]
  apply (baseIntegral p).add_mem
  · simp only [Polynomial.coeff_C]
    split_ifs
    · exact hC
    · exact (baseIntegral p).zero_mem
  · apply (baseIntegral p).mul_mem hL
    simp only [Polynomial.coeff_X]
    split_ifs <;> simp

/-- Proposition 3.1, coefficient content, proved by finite arithmetic truncation. -/
theorem content_coeff_proved (hp : 2 ≤ p) (K i : ℕ) :
    Nat.Coprime ((Delta p K).coeff i / (p : ℚ) ^ eK K).den p := by
  by_cases hK : K = 0
  · subst K
    exact content_coeff_zero p i
  · exact content_coeff_of_contentMatrix hp K (Nat.pos_of_ne_zero hK)
      (contentMatrix_coeff_integral hp K (Nat.pos_of_ne_zero hK)) i

end QZeta3
