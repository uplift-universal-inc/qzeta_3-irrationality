import QZeta3.Elementary

/-!
# The coefficientwise factor at primes dividing `p` (Proposition 3.1): route and API

**Status:** both statements of Proposition 3.1 are proved in `QZeta3.Frozen.Prop31`.
`QZeta3.ContentTruncation` proves coefficient content by finite arithmetic truncation, and
`QZeta3.Leading` proves the highest coefficient by Vandermonde factorization. This file
provides the elementary API about `F_K` used by those proofs.

* `F_monic`, `F_natDegree` : `F_K` is monic of degree `K`.
* `F_eval_zero` : `F_K(0) = (−1)^K p^{A_K}` (the single `p^{−A_K}` of the route).
* `sum_Icc_id_eq_AK` : `∑_{a=1}^{K} a = A_K`.

## Proof route (manuscript §3)

Work in `ℚ_ℓ` for a prime `ℓ ∣ p`.  With `g(y) = y(1+y)/(1−y)³`, `Z = ∑_{n ≥ 1} g(pⁿ)`
(ℓ-adically convergent) and `H(t) = ∑_{j ≥ 1} c_j t^j`, `c_j = j² p^j/(1 − p^j)`, the reciprocity
`g(1/y) = −g(y)` (`QZeta3.g_inv`) gives `S_a = −Z + H(p^a)`.  Writing `U = X + Z`, the moments
`M_k(X) = L_X(x^k/F_K)` become `M_0 = U/F_K(0) + R_0` and `M_k = −U h_{k−K} + R_k` (`k ≥ 1`) with
`h_t` the complete homogeneous symmetric polynomials of `p, …, p^K` and `R_k ∈ ℤ_ℓ` (divided
difference identities (3.5)).  Only the `(0,0)` entry carries `p^{−A_K}`, so every coefficient of
`det T` has valuation `≥ −A_K`, and `Δ_K = ±p^{A_K K} det T` gives `≥ A_K(K−1) = e_K`.  The
`U`-coefficient matrix is anti-triangular with determinant `±1/F_K(0)`, which gives the leading
coefficient.

The completed formal proof avoids local convergence: truncate `g` at degree `M = K²+K`,
prove that its remainder divided by `p^(M+1)` has denominator coprime to `p`, and absorb that
remainder using the uniform residue denominator bound. Finite divided differences then
prove exactly the required row-scaled integrality. All statements use `Rat.den`.
-/

open Polynomial Finset

namespace QZeta3

variable {p : ℕ}

theorem F_monic (p K : ℕ) : (F p K).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem F_natDegree (p K : ℕ) : (F p K).natDegree = K := by
  unfold F
  rw [Polynomial.natDegree_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _,
    Finset.sum_congr rfl fun a _ => Polynomial.natDegree_X_sub_C ((p : ℚ) ^ a)]
  simp

theorem sum_Icc_id_eq_AK (K : ℕ) : ∑ a ∈ Icc 1 K, a = AK K := by
  unfold AK
  exact (Nat.div_eq_of_eq_mul_left (by norm_num) (sum_Icc_id_mul_two K).symm).symm

/-- `F_K(0) = ∏_{a=1}^{K} (−p^a) = (−1)^K p^{A_K}`. -/
theorem F_eval_zero (p K : ℕ) : (F p K).eval 0 = (-1) ^ K * (p : ℚ) ^ AK K := by
  unfold F
  rw [Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  have h : ∀ a ∈ Icc 1 K, -((p : ℚ) ^ a) = (-1) * (p : ℚ) ^ a := fun a _ => by ring
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum, sum_Icc_id_eq_AK, Nat.card_Icc]
  simp

end QZeta3
