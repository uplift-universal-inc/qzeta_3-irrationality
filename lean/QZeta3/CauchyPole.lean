import QZeta3.CauchyAtInfinity
import QZeta3.CauchyExterior

open Filter Topology Finset

namespace QZeta3

noncomputable def cauchyKernel (p n : ℕ) (z : ℝ) : ℝ :=
  ((p : ℝ)⁻¹)^(n + 1) * (z + ((p : ℝ)⁻¹)^(n + 1)) /
    (z - ((p : ℝ)⁻¹)^(n + 1))^3

theorem summable_cauchyKernel_of_gt_q {p : ℕ} (hp : 2 ≤ p) {z : ℝ}
    (hz : (p : ℝ)⁻¹ < z) : Summable (fun n : ℕ => cauchyKernel p n z) := by
  let q := (p : ℝ)⁻¹
  have hq0 : 0 < q := inv_base_pos hp
  have hq1 : q < 1 := inv_base_lt_one hp
  have hz0 : 0 < z := lt_trans hq0 hz
  have hg : Summable (fun n : ℕ => q^(n + 1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => q^n) 1).mpr
      (hasSum_geometric_of_lt_one hq0.le hq1).summable
  have hbound : ∀ n : ℕ, 0 ≤ cauchyKernel p n z ∧
      cauchyKernel p n z ≤ q^(n + 1) * ((z + q) / (z - q)^3) := by
    intro n
    have hqn : 0 < q^(n + 1) := pow_pos hq0 _
    have hqnq : q^(n + 1) ≤ q := by
      simpa only [pow_one] using pow_le_pow_of_le_one hq0.le hq1.le (show 1 ≤ n + 1 by omega)
    have hdz : 0 < z - q^(n + 1) := by linarith
    change 0 ≤ q^(n + 1)*(z + q^(n + 1))/(z - q^(n + 1))^3 ∧ _
    constructor
    · positivity
    · unfold cauchyKernel
      change q^(n + 1)*(z + q^(n + 1))/(z - q^(n + 1))^3 ≤ _
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ hqn.le
      apply div_le_div₀ (by positivity) (by linarith) (by positivity)
      exact pow_le_pow_left₀ (by linarith) (by linarith) 3
  exact Summable.of_nonneg_of_le (fun n => (hbound n).1) (fun n => (hbound n).2)
    (hg.mul_right _)

/-- Removing finitely many geometric nodes leaves a rescaled copy of the same transform. -/
theorem cauchyKernel_shift {p : ℕ} (hp : 2 ≤ p) (N n : ℕ) (z : ℝ) :
    cauchyKernel p (n + N) z = (((p : ℝ)⁻¹)^N)⁻¹ *
      cauchyKernel p n (z / ((p : ℝ)⁻¹)^N) := by
  let t := ((p : ℝ)⁻¹)^N
  let a := ((p : ℝ)⁻¹)^(n + 1)
  have ht : t ≠ 0 := ne_of_gt (pow_pos (inv_base_pos hp) _)
  have hpow : ((p : ℝ)⁻¹)^(n + N + 1) = t * a := by
    dsimp [t, a]
    rw [← pow_add]
    congr 1
    omega
  have hplus : z + t*a = t*(z/t + a) := by field_simp
  have hminus : z - t*a = t*(z/t - a) := by field_simp
  simp only [cauchyKernel, hpow]
  change t*a*(z+t*a)/(z-t*a)^3 = t⁻¹*(a*(z/t+a)/(z/t-a)^3)
  rw [hplus, hminus, mul_pow]
  simp only [div_eq_mul_inv, mul_inv]
  field_simp [ht]

theorem cauchySeries_tail_eq {p : ℕ} (hp : 2 ≤ p) (N : ℕ) (z : ℝ) :
    (∑' n : ℕ, cauchyKernel p (n + N) z) = (((p : ℝ)⁻¹)^N)⁻¹ *
      cauchySeries p (z / ((p : ℝ)⁻¹)^N) := by
  simp_rw [cauchyKernel_shift hp]
  rw [tsum_mul_left]
  rfl

/-- Exact finite head plus rescaled tail, assuming convergence of that tail. -/
theorem cauchySeries_split {p : ℕ} (hp : 2 ≤ p) (N : ℕ) (z : ℝ)
    (hs : Summable (fun n : ℕ => cauchyKernel p n (z / ((p : ℝ)⁻¹)^N))) :
    cauchySeries p z = (∑ n ∈ range N, cauchyKernel p n z) +
      (((p : ℝ)⁻¹)^N)⁻¹ * cauchySeries p (z / ((p : ℝ)⁻¹)^N) := by
  have htail : Summable (fun n : ℕ => cauchyKernel p (n + N) z) := by
    simp only [cauchyKernel_shift hp]
    exact hs.mul_left _
  have hall : Summable (fun n : ℕ => cauchyKernel p n z) :=
    (summable_nat_add_iff (f := fun n : ℕ => cauchyKernel p n z) N).mp htail
  have heq := hall.sum_add_tsum_nat_add N
  rw [cauchySeries_tail_eq hp N z] at heq
  exact heq.symm

/-- Every lattice point is a genuine cubic pole, with nonzero leading coefficient. -/
theorem cauchySeries_cubic_pole {p : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    Tendsto (fun z : ℝ => (z - ((p : ℝ)⁻¹)^(m + 1))^3 * cauchySeries p z)
      (𝓝[≠] (((p : ℝ)⁻¹)^(m + 1)))
      (𝓝 (2 * (((p : ℝ)⁻¹)^(m + 1))^2)) := by
  let q := (p : ℝ)⁻¹
  let r := q^(m + 1)
  let t := q^(m + 2)
  let s := (range (m + 2)).erase m
  let R : ℝ → ℝ := fun z => (∑ n ∈ s, cauchyKernel p n z) + t⁻¹*cauchySeries p (z/t)
  have hq0 : 0 < q := inv_base_pos hp
  have hq1 : q < 1 := inv_base_lt_one hp
  have ht : t ≠ 0 := ne_of_gt (pow_pos hq0 _)
  have hscale : r/t = (p : ℝ) := by
    have hpw : t = r*q := by dsimp [r, t]; rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
    rw [hpw, div_mul_eq_div_div, div_self (ne_of_gt (pow_pos hq0 _)), one_div]
    exact inv_inv (p : ℝ)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hhead : ContinuousAt (fun z => ∑ n ∈ s, cauchyKernel p n z) r := by
    apply tendsto_finsetSum
    intro n hn
    have hnm : n ≠ m := (mem_erase.mp hn).1
    have hdiff : r - q^(n + 1) ≠ 0 := by
      apply sub_ne_zero.mpr
      intro heq
      have hmn := pow_right_injective₀ hq0 (ne_of_lt hq1) heq
      exact hnm (by omega)
    exact (continuousAt_const.mul (continuousAt_id.add continuousAt_const)).div
      ((continuousAt_id.sub continuousAt_const).pow 3) (pow_ne_zero 3 hdiff)
  have htail : ContinuousAt (fun z => t⁻¹*cauchySeries p (z/t)) r := by
    have hf : ContinuousAt (cauchySeries p) (r/t) := by
      rw [hscale]
      exact (analyticAt_cauchySeries_of_gt_one hp hp1).continuousAt
    exact continuousAt_const.mul (hf.comp (f := fun z : ℝ => z/t) (x := r) (continuousAt_id.div_const t))
  have hR : ContinuousAt R r := hhead.add htail
  have hnear : ∀ᶠ z : ℝ in 𝓝 r, q < z/t :=
    continuousAt_const.eventually_lt
      (show ContinuousAt (fun z : ℝ => z/t) r from continuousAt_id.div_const t)
      (by rw [hscale]; linarith)
  have hsplit : ∀ᶠ z : ℝ in 𝓝 r, cauchySeries p z = cauchyKernel p m z + R z := by
    filter_upwards [hnear] with z hz
    rw [cauchySeries_split hp (m + 2) z (summable_cauchyKernel_of_gt_q hp hz)]
    rw [← Finset.sum_erase_add (range (m + 2)) (fun n => cauchyKernel p n z) (a := m) (by simp)]
    dsimp [R, s, t]
    ring
  have hlim : Tendsto (fun z : ℝ => r*(z+r) + (z-r)^3*R z) (𝓝 r) (𝓝 (2*r^2)) := by
    have hc : ContinuousAt (fun z : ℝ => r*(z+r) + (z-r)^3*R z) r :=
      (continuousAt_const.mul (continuousAt_id.add continuousAt_const)).add
        (((continuousAt_id.sub continuousAt_const).pow 3).mul hR)
    convert hc.tendsto using 1
    ring_nf
  apply (hlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [hsplit.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzr
  have hzr' : z - r ≠ 0 := sub_ne_zero.mpr (by simpa only [r, q, inv_pow, Set.mem_compl_iff, Set.mem_singleton_iff] using hzr)
  rw [hz]
  change r*(z+r) + (z-r)^3*R z = (z-r)^3*(r*(z+r)/(z-r)^3 + R z)
  field_simp

end QZeta3
