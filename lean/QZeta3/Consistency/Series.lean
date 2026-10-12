import QZeta3.Elementary
import QZeta3.Content

/-!
# Consistency checks of the definitions

Checks on the *interpretation* of the formal definitions (not results claimed by the manuscript),
in the spirit of the `Consistency/` modules of recent formalisations:

* `xi_eq_tsum` : `xi p` is literally the manuscript's series `∑_{n ≥ 1} n²/(pⁿ − 1)`.
* `summable_term`, `hasSum_xi`, `xi_pos` (in `QZeta3.Elementary`) : the series converges, so the
  `tsum` is not the junk value `0`.
* `S_one` : `S_1 = p(p+1)/(p−1)³` (for `p = 2`: `S_1 = 6`, the root of the certificate
  `P_1(X) = X − 6`).
* `mu_zero`, `mu_succ` : the moments are `μ_0 = 0`, `μ_j = j²/(p^j − 1)`.
-/

open Finset

namespace QZeta3

theorem xi_eq_tsum (p : ℕ) :
    xi p = ∑' n : ℕ, ((n : ℝ) + 1) ^ 2 / ((p : ℝ) ^ (n + 1) - 1) := by
  simp [xi, term]

theorem S_one (p : ℕ) : S p 1 = ((p : ℚ) * ((p : ℚ) + 1)) / ((p : ℚ) - 1) ^ 3 := by
  unfold S
  simp

theorem S_one_two : S 2 1 = 6 := by
  rw [S_one]; norm_num

theorem mu_zero (p : ℕ) : mu p 0 = 0 := by simp [mu]

theorem mu_succ (p j : ℕ) : mu p (j + 1) = ((j + 1 : ℕ) : ℚ) ^ 2 / ((p : ℚ) ^ (j + 1) - 1) := by
  simp [mu]

end QZeta3

/-! ### The smallest determinant -/

namespace QZeta3

open Polynomial

/-- `Δ_1(X) = X − S_1`: the `1 × 1` case of the construction, matching the certificate
`P_1(X) = X − 6` at `p = 2`. -/
theorem Delta_one (p : ℕ) (hp : 2 ≤ p) : Delta p 1 = X - C (S p 1) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hF : F p 1 = X - C (p : ℚ) := by simp [F]
  have hdiv : (X ^ 0 : ℚ[X]) /ₘ F p 1 = 0 := by
    rw [pow_zero, (Polynomial.divByMonic_eq_zero_iff (F_monic p 1)).mpr]
    rw [hF, Polynomial.degree_X_sub_C, Polynomial.degree_one]
    exact zero_lt_one
  have hres : res p 1 0 1 = 1 := by simp [res, hF]
  have hAK : AK 1 = 1 := by decide
  have h1 : nrm p 1 * mLin p 1 0 = 1 := by
    simp only [nrm, mLin, hAK, Finset.Icc_self, Finset.sum_singleton, hres]
    field_simp
  have h2 : nrm p 1 * mConst p 1 0 = -(S p 1) := by
    simp only [nrm, mConst, hAK, Finset.Icc_self, Finset.sum_singleton, hres, hdiv, Lpoly,
      Polynomial.support_zero, Finset.sum_empty]
    field_simp
    ring
  unfold Delta
  rw [Matrix.det_fin_one]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, hankelLin, hankelConst,
    Matrix.of_apply, Fin.val_zero, add_zero, smul_eq_mul, h1, h2]
  simp [sub_eq_add_neg]

theorem Delta_one_two : Delta 2 1 = X - C 6 := by
  rw [Delta_one 2 (le_refl 2), S_one_two]

end QZeta3

/-! ### The `2 × 2` determinant at `p = 2`, against the exact certificate

`Δ_2(X) = −8X² + (2752/27)X − 2912/9 = (8/27)·P_2(X)` with the certificate
`P_2(X) = −(X − 6)(27X − 182)` of the companion bundle (`QZETA3_RESULTS.md`). The check is stated
through evaluation, which determines the polynomial. -/

namespace QZeta3

open Polynomial

theorem F_two_two : F 2 2 = (X - C 2) * (X - C 4) := by
  unfold F
  rw [show Finset.Icc 1 2 = {1, 2} from by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_singleton]
  norm_num

theorem S_two_two : S 2 2 = 182 / 27 := by
  unfold S
  rw [show Finset.Icc 1 2 = {1, 2} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num

theorem X_pow_two_divByMonic_F : (X ^ 2 : ℚ[X]) /ₘ F 2 2 = 1 := by
  have hmonic : (F 2 2).Monic := F_monic 2 2
  have hdeg : (F 2 2).degree = 2 := by
    rw [F_two_two, Polynomial.degree_mul, Polynomial.degree_X_sub_C, Polynomial.degree_X_sub_C]
    rfl
  have hr : (C 6 * X - C 8 : ℚ[X]).degree < (F 2 2).degree := by
    rw [hdeg]
    have : (C 6 * X - C 8 : ℚ[X]).degree ≤ 1 := by compute_degree
    exact lt_of_le_of_lt this (by decide)
  have hid : (C 6 * X - C 8 : ℚ[X]) + F 2 2 * 1 = X ^ 2 := by
    rw [F_two_two]
    simp only [map_ofNat]
    ring
  exact (Polynomial.div_modByMonic_unique 1 (C 6 * X - C 8) hmonic ⟨hid, hr⟩).1

theorem X_pow_lt_divByMonic_F (k : ℕ) (hk : k < 2) : (X ^ k : ℚ[X]) /ₘ F 2 2 = 0 := by
  rw [(Polynomial.divByMonic_eq_zero_iff (F_monic 2 2)).mpr]
  rw [F_two_two, Polynomial.degree_mul, Polynomial.degree_X_sub_C, Polynomial.degree_X_sub_C,
    Polynomial.degree_X_pow]
  exact_mod_cast hk

theorem eval_Delta_two_two (x : ℚ) :
    (Delta 2 2).eval x = -8 * x ^ 2 + 2752 / 27 * x - 2912 / 9 := by
  have hF' : ∀ y : ℚ, (derivative (F 2 2)).eval y = 2 * y - 6 := by
    intro y
    rw [F_two_two]
    simp [Polynomial.derivative_mul]
    ring
  have hres : ∀ k a : ℕ, res 2 2 k a = (2 : ℚ) ^ (a * k) / (2 * (2 : ℚ) ^ a - 6) := by
    intro k a
    simp only [res, hF']
    norm_num
  have hL0 : Lpoly 2 ((X ^ 0 : ℚ[X]) /ₘ F 2 2) = 0 := by
    rw [X_pow_lt_divByMonic_F 0 (by norm_num)]; simp [Lpoly]
  have hL1 : Lpoly 2 ((X ^ 1 : ℚ[X]) /ₘ F 2 2) = 0 := by
    rw [X_pow_lt_divByMonic_F 1 (by norm_num)]; simp [Lpoly]
  have hL2 : Lpoly 2 ((X ^ 2 : ℚ[X]) /ₘ F 2 2) = 0 := by
    rw [X_pow_two_divByMonic_F, Lpoly, ← Polynomial.C_1, Polynomial.support_C one_ne_zero]
    simp [mu]
  have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
  have hAK : AK 2 = 3 := by decide
  have hS1 : S 2 1 = 6 := S_one_two
  have hS2 : S 2 2 = 182 / 27 := S_two_two
  unfold Delta
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, hankelLin, hankelConst,
    Matrix.of_apply, Fin.val_zero, Fin.val_one, smul_eq_mul, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  simp only [nrm, mLin, mConst, hIcc, hAK, Finset.sum_insert (show (1 : ℕ) ∉ ({2} : Finset ℕ) by decide),
    Finset.sum_singleton, hres, hS1, hS2, zero_add, add_zero, hL0, hL1, hL2]
  norm_num
  ring

end QZeta3
