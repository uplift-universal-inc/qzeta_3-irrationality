import QZeta3.CauchyAtInfinity

open Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 2400000

namespace QZeta3

theorem summable_moment_mul_pow {p : ℕ} (hp : 2 ≤ p) {r : ℝ}
    (hr0 : 0 < r) (hrp : r < p) :
    Summable (fun n : ℕ => term p (n + 1) * r^n) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hqr0 : 0 < (p : ℝ)⁻¹*r := mul_pos (inv_pos.mpr hp0) hr0
  have hqr1 : (p : ℝ)⁻¹*r < 1 := by
    rw [inv_mul_lt_iff₀ hp0]
    simpa using hrp
  have hs : Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^2 * ((p : ℝ)⁻¹*r)^(n+1)) := (summable_nat_add_iff 1).mpr
    (summable_pow_mul_geometric_of_norm_lt_one (r := (p : ℝ)⁻¹*r) 2
      (by rw [Real.norm_eq_abs, abs_of_pos hqr0]; exact hqr1))
  have hbound : Summable (fun n : ℕ =>
      2 * ((((n+1 : ℕ) : ℝ))^2 * (p : ℝ)⁻¹^(n+1)) * r^n) := by
    convert hs.mul_left (2/r) using 1
    ext n
    rw [mul_pow, pow_succ r]
    field_simp
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (term_nonneg hp n) (le_of_lt (pow_pos hr0 n)))
    (fun n => mul_le_mul_of_nonneg_right (term_le hp n) (le_of_lt (pow_pos hr0 n))) hbound

theorem momentSeries_radius_ge {p : ℕ} (hp : 2 ≤ p) {r : ℝ≥0}
    (hr0 : 0 < r) (hrp : (r : ℝ) < p) :
    (r : ℝ≥0∞) ≤ (momentSeries p).radius := by
  apply (momentSeries p).le_radius_of_summable (r := r)
  simpa [momentSeries, FormalMultilinearSeries.ofScalars_norm,
    Real.norm_eq_abs, abs_of_nonneg (term_nonneg hp _)] using
      summable_moment_mul_pow hp (by exact_mod_cast hr0) hrp

theorem analyticAt_momentSeries_of_norm_lt {p : ℕ} (hp : 2 ≤ p) {u : ℝ}
    (hu : ‖u‖ < p) :
    AnalyticAt ℝ (fun v : ℝ => ∑' n : ℕ, term p (n + 1) * v^n) u := by
  obtain ⟨r, hur, hrp⟩ := exists_between hu
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hur
  have hr := momentSeries_radius_ge hp (r := ⟨r, le_of_lt hr0⟩) hr0 hrp
  have huR : u ∈ Metric.eball (0 : ℝ) (momentSeries p).radius := by
    apply mem_eball_zero_iff.mpr
    apply lt_of_lt_of_le _ hr
    exact ENNReal.coe_lt_coe.mpr hur
  have h := (momentSeries p).analyticOnNhd u huR
  convert h using 1
  ext v
  simpa [momentSeries, FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalars_sum_eq (fun n => term p (n + 1)) v).symm

end QZeta3
