import QZeta3.Elementary

/-!
# The decay bound and its asymptotics (proved)

`ε_K = C_K · K! · (12(2K−1)²)^K · p^{−(e_K + b_K)}` is the bound for `|P_K(ξ_p)|` obtained by
combining Propositions 2.1, 3.1 and 4.1 (§6 of the manuscript, with the `K!` prefactor of
`Matrix.det_le` in place of Hadamard's `√K^K`).  We prove the bookkeeping of §6:

  `log(b^K ε_K) ≤ −ε (log p) K³ + c K² log K + C'' K²`  (`ε = 11/18 − 321/(64π²)`),

so that `b^K ε_K → 0` for every positive integer `b`.
The general versions allow any cubic cost `α < 11/18`; the main theorem now uses the
fully proved two-prime sieve cost `α = 107/192`. The original sharp-cost wrappers are retained.
-/

open Filter Topology Real

namespace QZeta3

variable {p : ℕ}

/-- `ε_K = C_K · K! · (12(2K−1)²)^K · p^{−(e_K + b_K)}`. -/
noncomputable def epsK (p K : ℕ) : ℝ :=
  (CK p K : ℝ) * (K.factorial : ℝ) * (12 * (2 * (K : ℝ) - 1) ^ 2) ^ K *
    ((p : ℝ)⁻¹) ^ (eK K + bK K)

theorem epsK_pos (hp : 2 ≤ p) {K : ℕ} (hK : 1 ≤ K) : 0 < epsK p K := by
  unfold epsK
  have hCK : (0 : ℝ) < CK p K := by exact_mod_cast CK_pos hp K
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h12 : (0 : ℝ) < 12 * (2 * (K : ℝ) - 1) ^ 2 := by nlinarith
  have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    positivity
  have hf : (0 : ℝ) < K.factorial := by exact_mod_cast K.factorial_pos
  exact mul_pos (mul_pos (mul_pos hCK hf) (pow_pos h12 _)) (pow_pos hp0 _)

/-- The bookkeeping of §6: for `K ≥ 1`,
`log(b^K ε_K) ≤ −ε (log p) K³ + c K² log K + (log b + log 48 + log p + 3) K²`. -/
theorem log_pow_mul_epsK_le_of_cost (hp : 2 ≤ p) {α c : ℝ}
    (hC : ∀ K : ℕ, 2 ≤ K → Real.log (CK p K) ≤
      α * (K : ℝ) ^ 3 * log p + c * (K : ℝ) ^ 2 * log K)
    (b : ℕ) (hb : 0 < b) (K : ℕ) (hK : 2 ≤ K) :
    Real.log ((b : ℝ) ^ K * epsK p K) ≤
      -(11/18-α) * (K : ℝ) ^ 3 * log p + c * (K : ℝ) ^ 2 * log K +
        (log b + log 48 + log p + 3) * (K : ℝ) ^ 2 := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hKpos : (0 : ℝ) < K := by linarith
  have hlogK0 : 0 ≤ log K := Real.log_nonneg hK1
  have hlogK : log K ≤ K := by
    have := Real.log_le_sub_one_of_pos hKpos
    linarith
  have hlogp : 0 < log p := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hlogb : 0 ≤ log b := Real.log_natCast_nonneg b
  have hlog48 : 0 ≤ log (48 : ℝ) := Real.log_nonneg (by norm_num)
  have hCK : (0 : ℝ) < CK p K := by exact_mod_cast CK_pos hp K
  have hfact : (0 : ℝ) < K.factorial := by exact_mod_cast K.factorial_pos
  have h12 : (0 : ℝ) < 12 * (2 * (K : ℝ) - 1) ^ 2 := by nlinarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpinv : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  -- expand the logarithm of the product
  have hlog : Real.log ((b : ℝ) ^ K * epsK p K) =
      K * log b + log (CK p K : ℝ) + log (K.factorial : ℝ) + K * log (12 * (2 * (K : ℝ) - 1) ^ 2)
        - ((eK K : ℝ) + bK K) * log p := by
    unfold epsK
    have hA : (0 : ℝ) < (12 * (2 * (K : ℝ) - 1) ^ 2) ^ K := pow_pos h12 _
    have hP : (0 : ℝ) < ((p : ℝ)⁻¹) ^ (eK K + bK K) := pow_pos hpinv _
    rw [Real.log_mul (pow_pos hbR _).ne' (mul_pos (mul_pos (mul_pos hCK hfact) hA) hP).ne',
      Real.log_mul (mul_pos (mul_pos hCK hfact) hA).ne' hP.ne',
      Real.log_mul (mul_pos hCK hfact).ne' hA.ne', Real.log_mul hCK.ne' hfact.ne',
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_inv]
    push_cast
    ring
  -- the individual estimates
  have hfact_le : log (K.factorial : ℝ) ≤ K * log K := by
    have h1 : (K.factorial : ℝ) ≤ (K : ℝ) ^ K := by exact_mod_cast Nat.factorial_le_pow K
    calc log (K.factorial : ℝ) ≤ log ((K : ℝ) ^ K) := Real.log_le_log hfact h1
      _ = K * log K := Real.log_pow K K
  have hA_le : log (12 * (2 * (K : ℝ) - 1) ^ 2) ≤ log 48 + 2 * log K := by
    have h1 : 12 * (2 * (K : ℝ) - 1) ^ 2 ≤ 48 * (K : ℝ) ^ 2 := by nlinarith
    calc log (12 * (2 * (K : ℝ) - 1) ^ 2) ≤ log (48 * (K : ℝ) ^ 2) := Real.log_le_log h12 h1
      _ = log 48 + 2 * log K := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        push_cast
        ring
  have he : (11 / 18 : ℝ) * ((K : ℝ) ^ 3 - K) ≤ (eK K : ℝ) + bK K := by
    have h1 := eK_cast (show 1 ≤ K by omega)
    have h2 := bK_ge K
    rw [h1]
    linarith
  have hCKb := hC K hK
  -- lower-order terms are dominated by `K²` (`K ≥ 1`, `0 ≤ log K ≤ K`)
  have hK_sq : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
  have hKlogK : (K : ℝ) * log K ≤ (K : ℝ) ^ 2 := by nlinarith
  have hb1 : (K : ℝ) * log b ≤ log b * (K : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hK_sq hlogb; linarith
  have h48 : (K : ℝ) * log 48 ≤ log 48 * (K : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hK_sq hlog48; linarith
  have hp1 : (11 / 18 : ℝ) * ((K : ℝ) * log p) ≤ log p * (K : ℝ) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hK_sq hlogp.le
    have h2 : 0 ≤ (K : ℝ) * log p := by positivity
    nlinarith
  have hA2 : (K : ℝ) * log (12 * (2 * (K : ℝ) - 1) ^ 2) ≤ K * log 48 + 2 * (K * log K) := by
    have := mul_le_mul_of_nonneg_left hA_le hKpos.le; linarith
  have he' : (11 / 18 : ℝ) * (((K : ℝ) ^ 3 - K) * log p) ≤ ((eK K : ℝ) + bK K) * log p := by
    have := mul_le_mul_of_nonneg_right he hlogp.le; linarith
  rw [hlog]
  nlinarith [hfact_le, hA2, hb1, h48, hp1, he', hCKb, hKlogK, hK_sq]

/-- `b^K ε_K → 0` for every positive integer `b`, given the growth bound on `log C_K`. -/
theorem tendsto_pow_mul_epsK_of_cost (hp : 2 ≤ p) {α c : ℝ}
    (hα : α < 11/18)
    (hC : ∀ K : ℕ, 2 ≤ K → Real.log (CK p K) ≤
      α * (K : ℝ) ^ 3 * log p + c * (K : ℝ) ^ 2 * log K)
    (b : ℕ) (hb : 0 < b) :
    Tendsto (fun K : ℕ => (b : ℝ) ^ K * epsK p K) atTop (𝓝 0) := by
  set C'' : ℝ := log b + log 48 + log p + 3 with hC''
  have hlogp : 0 < log p := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hneg : -(11/18-α) * log p < 0 := by
    have : 0 < 11/18-α := sub_pos.mpr hα
    nlinarith
  have hf : Tendsto
      (fun K : ℕ => -(11/18-α) * (K : ℝ) ^ 3 * log p + c * (K : ℝ) ^ 2 * log K + C'' * (K : ℝ) ^ 2)
      atTop atBot := by
    have h1 : Tendsto (fun K : ℕ => (K : ℝ) ^ 3) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun K : ℕ => log (K : ℝ) / (K : ℝ)) atTop (𝓝 0) := by
      have := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
      simpa [Function.comp_def] using this
    have h2' : Tendsto (fun K : ℕ => C'' / (K : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat C''
    have h3 : Tendsto (fun K : ℕ => -(11/18-α) * log p + c * (log (K : ℝ) / K) + C'' / K) atTop
        (𝓝 (-(11/18-α) * log p)) := by
      have := ((h2.const_mul c).const_add (-(11/18-α) * log p)).add h2'
      simpa using this
    have h4 := h1.atTop_mul_neg hneg h3
    refine h4.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with K hK
    have hK0 : (K : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ K := by exact_mod_cast hK
      linarith
    field_simp
  have hexp : Tendsto (fun K : ℕ => Real.exp
      (-(11/18-α) * (K : ℝ) ^ 3 * log p + c * (K : ℝ) ^ 2 * log K + C'' * (K : ℝ) ^ 2))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with K hK
    exact le_of_lt (mul_pos (pow_pos (by exact_mod_cast hb) _) (epsK_pos hp hK))
  · filter_upwards [eventually_ge_atTop 2] with K hK
    have hpos : 0 < (b : ℝ) ^ K * epsK p K :=
      mul_pos (pow_pos (by exact_mod_cast hb) _) (epsK_pos hp (by omega))
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr (log_pow_mul_epsK_le_of_cost hp hC b hb K hK)

/-- Original sharp-cost bookkeeping statement, recovered from the general cost bound. -/
theorem log_pow_mul_epsK_le (hp : 2 ≤ p) {c : ℝ}
    (hC : ∀ K : ℕ, 2 ≤ K → Real.log (CK p K) ≤
      321 / (64 * π ^ 2) * (K : ℝ) ^ 3 * log p + c * (K : ℝ) ^ 2 * log K)
    (b : ℕ) (hb : 0 < b) (K : ℕ) (hK : 2 ≤ K) :
    Real.log ((b : ℝ) ^ K * epsK p K) ≤
      -margin * (K : ℝ) ^ 3 * log p + c * (K : ℝ) ^ 2 * log K +
        (log b + log 48 + log p + 3) * (K : ℝ) ^ 2 := by
  simpa only [margin] using log_pow_mul_epsK_le_of_cost hp hC b hb K hK

/-- Original sharp-cost convergence statement, recovered from the general cost bound. -/
theorem tendsto_pow_mul_epsK (hp : 2 ≤ p) {c : ℝ}
    (hC : ∀ K : ℕ, 2 ≤ K → Real.log (CK p K) ≤
      321 / (64 * π ^ 2) * (K : ℝ) ^ 3 * log p + c * (K : ℝ) ^ 2 * log K)
    (b : ℕ) (hb : 0 < b) :
    Tendsto (fun K : ℕ => (b : ℝ) ^ K * epsK p K) atTop (𝓝 0) := by
  exact tendsto_pow_mul_epsK_of_cost hp (sub_pos.mp margin_pos) hC b hb

end QZeta3
