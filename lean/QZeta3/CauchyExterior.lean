import QZeta3.CauchyAtInfinity

open Filter Topology
open scoped ENNReal NNReal

namespace QZeta3

theorem analyticAt_momentSeries_unit {p : ℕ} (hp : 2 ≤ p) {u : ℝ}
    (hu : ‖u‖ < 1) :
    AnalyticAt ℝ (fun v : ℝ => ∑' n : ℕ, term p (n+1)*v^n) u := by
  have huR : u ∈ Metric.eball (0 : ℝ) (momentSeries p).radius := by
    apply mem_eball_zero_iff.mpr
    apply lt_of_lt_of_le _ (momentSeries_radius_ge_one hp)
    exact ENNReal.coe_lt_coe.mpr hu
  have h := (momentSeries p).analyticOnNhd u huR
  convert h using 1
  ext v
  simpa [momentSeries, FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalars_sum_eq (fun n => term p (n+1)) v).symm

theorem analyticAt_cauchySeries_of_gt_one {p : ℕ} (hp : 2 ≤ p) {z : ℝ}
    (hz : 1 < z) : AnalyticAt ℝ (cauchySeries p) z := by
  have hz0 : z ≠ 0 := by linarith
  have hinv : ‖z⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith))]
    exact inv_lt_one_of_one_lt₀ hz
  have hi : AnalyticAt ℝ (fun w : ℝ => w⁻¹) z := analyticAt_id.inv hz0
  have h := (hi.pow 2).mul ((analyticAt_momentSeries_unit hp hinv).comp hi)
  apply h.congr
  have hn : ∀ᶠ w : ℝ in 𝓝 z, 1 < w := eventually_gt_nhds hz
  filter_upwards [hn] with w hw
  have hw0 : w ≠ 0 := by linarith
  have hwinv : ‖w⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith))]
    exact inv_lt_one_of_one_lt₀ hw
  simpa using (cauchySeries_inv_eq hp hwinv (inv_ne_zero hw0)).symm

end QZeta3
