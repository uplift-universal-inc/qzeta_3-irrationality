import QZeta3.Purity
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Meromorphic.Basic

open Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 800000

namespace QZeta3

noncomputable def cauchySeries (p : ℕ) (z : ℝ) : ℝ :=
  ∑' m : ℕ, ((p : ℝ)⁻¹) ^ (m + 1) * (z + ((p : ℝ)⁻¹) ^ (m + 1)) /
    (z - ((p : ℝ)⁻¹) ^ (m + 1)) ^ 3

noncomputable def momentSeries (p : ℕ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n => term p (n + 1))

theorem momentSeries_radius_ge_one {p : ℕ} (hp : 2 ≤ p) :
    (1 : ℝ≥0∞) ≤ (momentSeries p).radius := by
  apply (momentSeries p).le_radius_of_summable (r := 1)
  simpa [momentSeries, FormalMultilinearSeries.ofScalars_norm,
    Real.norm_eq_abs, abs_of_nonneg (term_nonneg hp _)] using summable_term hp

theorem analyticAt_momentSeries {p : ℕ} (hp : 2 ≤ p) :
    AnalyticAt ℝ (fun u : ℝ => ∑' n : ℕ, term p (n + 1) * u^n) 0 := by
  have h := (momentSeries p).hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) (momentSeries_radius_ge_one hp))
  convert h.analyticAt using 1
  ext u
  simpa [momentSeries, FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalars_sum_eq (fun n => term p (n + 1)) u).symm

/-- The two positive geometric-lattice indices form an absolutely convergent double series. -/
theorem summable_geometric_lattice {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun nm : ℕ × ℕ => ((nm.1 + 1 : ℕ) : ℝ)^2 *
      ((p : ℝ)⁻¹)^((nm.1 + 1) * (nm.2 + 1))) := by
  apply (summable_prod_of_nonneg (fun nm => by positivity)).mpr
  constructor
  · intro n
    exact (hasSum_geometric_lattice_row hp n).summable
  · convert summable_term hp using 1
    ext n
    exact (hasSum_geometric_lattice_row hp n).tsum_eq

theorem cauchySeries_inv_eq {p : ℕ} (hp : 2 ≤ p) {u : ℝ}
    (hu : ‖u‖ < 1) (hu0 : u ≠ 0) :
    cauchySeries p u⁻¹ = u^2 * ∑' n : ℕ, term p (n + 1) * u^n := by
  let f : ℕ × ℕ → ℝ := fun nm => ((nm.1 + 1 : ℕ) : ℝ)^2 *
    ((p : ℝ)⁻¹)^((nm.1 + 1) * (nm.2 + 1)) * u^nm.1
  have hf : Summable f := by
    apply Summable.of_norm_bounded (summable_geometric_lattice hp)
    intro nm
    dsimp [f]
    rw [abs_mul, abs_of_nonneg (by positivity :
      0 ≤ ((nm.1 + 1 : ℕ) : ℝ)^2 * ((p : ℝ)⁻¹)^((nm.1 + 1)*(nm.2+1)))]
    apply mul_le_of_le_one_right (by positivity)
    rw [abs_pow, ← Real.norm_eq_abs]
    exact pow_le_one₀ (norm_nonneg _) (le_of_lt hu)
  have hrow (n : ℕ) : ∑' m : ℕ, f (n,m) = term p (n+1) * u^n := by
    exact ((hasSum_geometric_lattice_row hp n).mul_right (u^n)).tsum_eq
  have hcol (m : ℕ) : ∑' n : ℕ, f (n,m) =
      ((p : ℝ)⁻¹)^(m+1) * (1 + ((p : ℝ)⁻¹)^(m+1)*u) /
        (1 - ((p : ℝ)⁻¹)^(m+1)*u)^3 := by
    let q : ℝ := ((p : ℝ)⁻¹)^(m+1)
    have hq : 0 < q := by dsimp [q]; exact pow_pos (inv_base_pos hp) _
    have hq1 : q < 1 := inv_base_pow_lt_one hp (by omega)
    have hqu : ‖q*u‖ < 1 := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos hq]
      nlinarith [norm_nonneg u]
    have hs := hasSum_sq_mul_geometric_of_norm_lt_one hqu
    have hshift : HasSum (fun n : ℕ => ((n+1 : ℕ) : ℝ)^2 * (q*u)^(n+1))
        ((q*u)*(1+q*u)/(1-q*u)^3) := by
      apply (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℝ)^2 * (q*u)^n) 1).mpr
      simpa using hs
    have heq : (fun n : ℕ => f (n,m)) =
        (fun n : ℕ => ((n+1 : ℕ) : ℝ)^2 * (q*u)^(n+1) * u⁻¹) := by
      ext n
      dsimp [f, q]
      rw [mul_pow, ← pow_mul, Nat.mul_comm (m+1) (n+1), pow_succ u]
      field_simp
    rw [heq, (hshift.mul_right u⁻¹).tsum_eq]
    dsimp [q]
    field_simp
  unfold cauchySeries
  rw [← funext hrow, ← hf.tsum_comm, ← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [hcol]
  have hz : 1 - ((p : ℝ)⁻¹)^(m+1)*u ≠ 0 := by
    have hq : 0 < ((p : ℝ)⁻¹)^(m+1) := pow_pos (inv_base_pos hp) _
    have hq1 : ((p : ℝ)⁻¹)^(m+1) < 1 := inv_base_pow_lt_one hp (by omega)
    have hule : u ≤ ‖u‖ := by simpa [Real.norm_eq_abs] using le_abs_self u
    nlinarith [norm_nonneg u]
  have hzu : u⁻¹ - ((p : ℝ)⁻¹)^(m+1) ≠ 0 := by
    intro he
    apply hz
    rw [← sub_eq_zero.mp he, inv_mul_cancel₀ hu0, sub_self]
  field_simp

theorem meromorphicAt_cauchySeries_inv {p : ℕ} (hp : 2 ≤ p) :
    MeromorphicAt (fun u : ℝ => cauchySeries p u⁻¹) 0 := by
  have h : AnalyticAt ℝ (fun u : ℝ => u^2 * ∑' n : ℕ, term p (n+1)*u^n) 0 :=
    (analyticAt_id.pow 2).mul (analyticAt_momentSeries hp)
  apply h.meromorphicAt.congr
  have hn : ∀ᶠ u : ℝ in 𝓝 (0 : ℝ), ‖u‖ < 1 := by
    exact (continuous_norm.continuousAt.eventually_lt continuousAt_const (by norm_num))
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu hu0
  exact (cauchySeries_inv_eq hp hu (by simpa using hu0)).symm

end QZeta3
