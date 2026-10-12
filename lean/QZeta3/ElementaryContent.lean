import QZeta3.ContentTruncation
import QZeta3.GaussianIdentity

/-!
# Elementary Gaussian-binomial route to coefficient content

The alternative arithmetic argument uses integer-valued monomial residue sums,
computed by the finite Gaussian-binomial identity. Finite linearity gives the
polynomial residue assertion needed for the moment matrix. The finite geometric
tail estimates and determinant normalization are shared with the first proof;
none of its divided-difference integrality assertions is used here.
-/

open Polynomial Finset

namespace QZeta3

variable {p : ℕ}

section GaussianInput

variable (hGaussian : ∀ K d : ℕ, ∃ z : ℤ,
  (∑ a ∈ Icc 1 K, ((p : ℚ) ^ a) ^ d /
    (derivative (F p K)).eval ((p : ℚ) ^ a)) = z)

include hGaussian

/-- Finite linearity upgrades the integer-valued Gaussian monomial identity to
polynomials whose coefficients are integral at every prime dividing the base. -/
theorem elementary_residue_sum_mem (K : ℕ) (f : ℚ[X])
    (hf : ∀ i, f.coeff i ∈ baseIntegral p) :
    (∑ a ∈ Icc 1 K, f.eval ((p : ℚ) ^ a) /
      (derivative (F p K)).eval ((p : ℚ) ^ a)) ∈ baseIntegral p := by
  have heq : (∑ a ∈ Icc 1 K, f.eval ((p : ℚ) ^ a) /
      (derivative (F p K)).eval ((p : ℚ) ^ a)) =
      ∑ j ∈ range (f.natDegree + 1), f.coeff j *
        ∑ a ∈ Icc 1 K, ((p : ℚ) ^ a) ^ j /
          (derivative (F p K)).eval ((p : ℚ) ^ a) := by
    simp_rw [Polynomial.eval_eq_sum_range, Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [heq]
  apply (baseIntegral p).sum_mem
  intro j _
  apply (baseIntegral p).mul_mem (hf j)
  obtain ⟨z, hz⟩ := hGaussian K j
  rw [hz]
  exact intCast_mem (baseIntegral p) z

/-- The `X` coefficient of every positive-index moment is integral at the base. -/
theorem elementary_mLin_mem (hp : 2 ≤ p) (K k : ℕ) (hk : 0 < k) :
    mLin p K k ∈ baseIntegral p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hexp : ∀ a : ℕ, a * k = a * (k - 1) + a := by
    intro a
    have h : k = (k - 1) + 1 := by omega
    rw [h]
    simp only [Nat.add_sub_cancel, mul_add, mul_one]
  have hsum : mLin p K k = -(∑ a ∈ Icc 1 K,
      (X ^ (k - 1) : ℚ[X]).eval ((p : ℚ) ^ a) /
        (derivative (F p K)).eval ((p : ℚ) ^ a)) := by
    unfold mLin
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    simp only [res, Polynomial.eval_pow, Polynomial.eval_X, ← pow_mul]
    rw [hexp, pow_add, div_right_comm, mul_div_cancel_right₀ _ (pow_ne_zero a hp0)]
  rw [hsum]
  apply (baseIntegral p).neg_mem
  apply elementary_residue_sum_mem hGaussian K
  intro i
  simp only [Polynomial.coeff_X_pow]
  split_ifs <;> simp

/-- The polynomial part of the translated residue sum is integral for every moment index,
including zero. -/
theorem elementary_localTrunc_residue_mem (hp : 2 ≤ p) (K k M : ℕ) :
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
  exact elementary_residue_sum_mem hGaussian K f hf

/-- The constant moments become integral after subtracting the finite local
translation times their linear coefficient. This is the arithmetic heart of
Proposition 3.1, proved using a finite truncation rather than a convergent local series. -/
theorem elementary_mConst_sub_translation_mem (hp : 2 ≤ p) (K k : ℕ) :
    mConst p K k - (localTruncPolynomial p (K*K+K)).eval 1 * mLin p K k ∈
      baseIntegral p := by
  have hQ := quotient_moment_mem_baseIntegral p K k (show 1 ≤ p by omega)
  have hH := elementary_localTrunc_residue_mem hGaussian hp K k (K*K+K)
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

theorem elementary_mConst_mem (hp : 2 ≤ p) (K k : ℕ) (hk : 0 < k) :
    mConst p K k ∈ baseIntegral p := by
  have hZ := eval_mem_baseIntegral p (localTruncPolynomial p (K*K+K))
    (localTruncPolynomial_coeff_mem hp (K*K+K)) 1 (baseIntegral p).one_mem
  have h := (baseIntegral p).add_mem (elementary_mConst_sub_translation_mem hGaussian hp K k)
    ((baseIntegral p).mul_mem hZ (elementary_mLin_mem hGaussian hp K k hk))
  simpa only [sub_add_cancel] using h

theorem elementary_scaled_mConst_zero_mem (hp : 2 ≤ p) (K : ℕ) (hK : 0 < K) :
    (p : ℚ) ^ AK K * mConst p K 0 ∈ baseIntegral p := by
  have hZ := eval_mem_baseIntegral p (localTruncPolynomial p (K*K+K))
    (localTruncPolynomial_coeff_mem hp (K*K+K)) 1 (baseIntegral p).one_mem
  have hR := (baseIntegral p).mul_mem
    ((baseIntegral p).pow_mem (natCast_mem (baseIntegral p) p) (AK K))
    (elementary_mConst_sub_translation_mem hGaussian hp K 0)
  have hL : (p : ℚ) ^ AK K * mLin p K 0 ∈ baseIntegral p := by
    rw [scaled_mLin_zero hp K hK]
    exact (baseIntegral p).pow_mem ((baseIntegral p).neg_mem (baseIntegral p).one_mem) K
  have h := (baseIntegral p).add_mem hR ((baseIntegral p).mul_mem hZ hL)
  convert h using 1
  ring

/-- Every coefficient of the matrix obtained by scaling the exceptional row is integral. -/
theorem elementary_contentMatrix_coeff_integral (hp : 2 ≤ p) (K : ℕ) (hK : 0 < K) :
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
      simpa only [s, ha, ite_true] using elementary_scaled_mConst_zero_mem hGaussian hp K hK
    · exact (baseIntegral p).mul_mem hs (elementary_mConst_mem hGaussian hp K _ (Nat.pos_of_ne_zero hk))
  have hL : s * mLin p K (a.val + b.val) ∈ baseIntegral p := by
    by_cases hk : a.val + b.val = 0
    · have ha : a.val = 0 := by omega
      rw [hk]
      simp only [s, ha, ite_true, scaled_mLin_zero hp K hK]
      exact (baseIntegral p).pow_mem ((baseIntegral p).neg_mem (baseIntegral p).one_mem) K
    · exact (baseIntegral p).mul_mem hs (elementary_mLin_mem hGaussian hp K _ (Nat.pos_of_ne_zero hk))
  have heq : (contentMatrix p K) a b =
      C (s * mConst p K (a.val + b.val)) + C (s * mLin p K (a.val + b.val)) * X := by
    unfold contentMatrix momentMatrix
    dsimp [s]
    split_ifs <;> simp only [map_mul, one_mul]
    ring
  rw [heq, Polynomial.coeff_add, Polynomial.coeff_C_mul]
  apply (baseIntegral p).add_mem
  · simp only [Polynomial.coeff_C]
    split_ifs
    · exact hC
    · exact (baseIntegral p).zero_mem
  · apply (baseIntegral p).mul_mem hL
    simp only [Polynomial.coeff_X]
    split_ifs <;> simp

/-- The Gaussian-binomial arithmetic route proves the original coefficientwise
content assertion. The finite geometric-tail estimates, polynomial-quotient
integrality, exceptional partial-fractions identity, empty-matrix case, and
determinant normalization are shared with the first proof. The polynomial
residue integrality is supplied by the Gaussian identity. -/
theorem content_coeff_of_gaussian (hp : 2 ≤ p) (K i : ℕ) :
    Nat.Coprime ((Delta p K).coeff i / (p : ℚ) ^ eK K).den p := by
  by_cases hK : K = 0
  · subst K
    exact content_coeff_zero p i
  · exact content_coeff_of_contentMatrix hp K (Nat.pos_of_ne_zero hK)
      (elementary_contentMatrix_coeff_integral hGaussian hp K (Nat.pos_of_ne_zero hK)) i

end GaussianInput

/-- Proposition 3.1 by the finite Gaussian-binomial arithmetic proof.
This proof does not depend on the original divided-difference integrality
lemma or the original coefficient-content theorem. -/
theorem content_coeff_elementary (hp : 2 ≤ p) (K i : ℕ) :
    Nat.Coprime ((Delta p K).coeff i / (p : ℚ) ^ eK K).den p :=
  content_coeff_of_gaussian (gaussian_residue_integral hp) hp K i

end QZeta3
