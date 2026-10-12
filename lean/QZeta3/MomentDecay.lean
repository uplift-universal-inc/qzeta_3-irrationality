import QZeta3.CauchyAtInfinity

open Finset Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 800000

namespace QZeta3

theorem term_nonneg_all {p : ℕ} (hp : 2 ≤ p) (n : ℕ) : 0 ≤ term p n := by
  cases n with
  | zero => simp [term]
  | succ n => exact term_nonneg hp n

theorem summable_term_all {p : ℕ} (hp : 2 ≤ p) : Summable (term p) :=
  (summable_nat_add_iff 1).mp (summable_term hp)

noncomputable def shiftedMoments (p k : ℕ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n => term p (n+k))

theorem shiftedMoments_radius_ge_one {p : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    (1 : ℝ≥0∞) ≤ (shiftedMoments p k).radius := by
  apply (shiftedMoments p k).le_radius_of_summable (r := 1)
  simpa [shiftedMoments, FormalMultilinearSeries.ofScalars_norm,
    Real.norm_eq_abs, abs_of_nonneg (term_nonneg_all hp _)] using
      (summable_nat_add_iff k).mpr (summable_term_all hp)

theorem analyticAt_shiftedMoments {p : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    AnalyticAt ℝ (fun u : ℝ => ∑' n : ℕ, term p (n+k) * u^n) 0 := by
  have h := (shiftedMoments p k).hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) (shiftedMoments_radius_ge_one hp k))
  convert h.analyticAt using 1
  ext u
  simpa [shiftedMoments, FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalars_sum_eq (fun n => term p (n+k)) u).symm

theorem summable_moment_power {p : ℕ} (hp : 2 ≤ p) {u : ℝ} (hu : ‖u‖ < 1) :
    Summable (fun n : ℕ => term p n * u^n) := by
  apply Summable.of_norm_bounded (summable_term_all hp)
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (term_nonneg_all hp n), abs_pow, ← Real.norm_eq_abs]
  exact mul_le_of_le_one_right (term_nonneg_all hp n)
    (pow_le_one₀ (norm_nonneg _) (le_of_lt hu))

theorem cauchySeries_inv_eq_full {p : ℕ} (hp : 2 ≤ p) {u : ℝ}
    (hu : ‖u‖ < 1) (hu0 : u ≠ 0) :
    cauchySeries p u⁻¹ = u * ∑' n : ℕ, term p n * u^n := by
  have h0 : term p 0 = 0 := by simp [term]
  have hshift : (∑' n : ℕ, term p (n+1)*u^(n+1)) =
      (∑' n : ℕ, term p (n+1)*u^n)*u := by
    rw [← tsum_mul_right]
    apply tsum_congr
    intro n
    rw [pow_succ]
    ring
  rw [cauchySeries_inv_eq hp hu hu0,
    (summable_moment_power hp hu).tsum_eq_zero_add, h0, zero_mul, zero_add, hshift]
  ring

noncomputable def momentPolynomial (p k : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ range k, term p j * z^(k-1-j)

theorem cauchySeries_remainder {p : ℕ} (hp : 2 ≤ p) {u : ℝ}
    (hu : ‖u‖ < 1) (hu0 : u ≠ 0) (k : ℕ) :
    cauchySeries p u⁻¹ * (u⁻¹)^k - momentPolynomial p k u⁻¹ =
      u * ∑' n : ℕ, term p (n+k) * u^n := by
  have hsplit := (summable_moment_power hp hu).sum_add_tsum_nat_add k
  have htail : (∑' n : ℕ, term p (n+k) * u^(n+k)) =
      u^k * ∑' n : ℕ, term p (n+k)*u^n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [pow_add]
    ring
  rw [htail] at hsplit
  have hpoly : u^k * momentPolynomial p k u⁻¹ =
      u * ∑ j ∈ range k, term p j * u^j := by
    unfold momentPolynomial
    rw [mul_sum, mul_sum]
    apply sum_congr rfl
    intro j hj
    have hjk : j < k := mem_range.mp hj
    have he : k = (k-1-j) + (j+1) := by omega
    have hpow : u^k = u^(k-1-j) * u^(j+1) := by rw [← pow_add, ← he]
    have hc : u^(k-1-j)*(u⁻¹)^(k-1-j) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hu0, one_pow]
    calc u^k * (term p j * (u⁻¹)^(k-1-j)) =
        term p j * u^(j+1) * (u^(k-1-j)*(u⁻¹)^(k-1-j)) := by rw [hpow]; ring
      _ = u * (term p j * u^j) := by rw [hc, pow_succ]; ring

  apply (mul_left_cancel₀ (pow_ne_zero k hu0))
  rw [mul_sub, hpoly, cauchySeries_inv_eq_full hp hu hu0]
  have hinv : u^k * (u⁻¹)^k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hu0, one_pow]
  calc u^k * ((u * ∑' n : ℕ, term p n*u^n) * (u⁻¹)^k) -
          u * ∑ j ∈ range k, term p j*u^j =
        u * (∑' n : ℕ, term p n*u^n) * (u^k*(u⁻¹)^k) -
          u * ∑ j ∈ range k, term p j*u^j := by ring
    _ = _ := by rw [hinv, ← hsplit]; ring

theorem tendsto_cauchySeries_monomial_sub {p : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    Tendsto (fun z : ℝ => cauchySeries p z * z^k - momentPolynomial p k z)
      atTop (𝓝 0) := by
  have htail := (analyticAt_shiftedMoments hp k).continuousAt.tendsto.comp
    (tendsto_inv_atTop_zero : Tendsto (fun z : ℝ => z⁻¹) atTop (𝓝 0))
  have hprod := (tendsto_inv_atTop_zero : Tendsto (fun z : ℝ => z⁻¹) atTop (𝓝 0)).mul htail
  simp only [zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
  have hz0 : z ≠ 0 := by linarith
  have hzinv : ‖z⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith))]
    exact inv_lt_one_of_one_lt₀ hz
  simpa using (cauchySeries_remainder hp hzinv (inv_ne_zero hz0) k).symm

theorem mu_cast_eq_term (p j : ℕ) : (mu p j : ℝ) = term p j := by
  cases j with
  | zero => simp [mu, term]
  | succ j => simp [mu, term]

theorem momentPolynomial_eq_mu (p k : ℕ) (z : ℝ) :
    momentPolynomial p k z = ∑ j ∈ range k, (mu p j : ℝ)*z^(k-1-j) := by
  simp only [momentPolynomial, mu_cast_eq_term]

end QZeta3
