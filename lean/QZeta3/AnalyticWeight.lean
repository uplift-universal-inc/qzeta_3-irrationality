import QZeta3.Functional
import QZeta3.CyclotomicBounds

/-! The rational weight in the triple-root determinant estimate. -/

open Finset Filter Topology

namespace QZeta3

theorem theta_mul {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    theta (f * g) x = theta f x * g x + f x * theta g x := by
  simp only [theta, deriv_mul hf hg]
  ring

theorem theta_sq_mul {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    theta (theta (f * g)) x = theta (theta f) x * g x +
      2 * theta f x * theta g x + f x * theta (theta g) x := by
  have he : theta (f * g) =ᶠ[𝓝 x] theta f * g + f * theta g := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact theta_mul (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  rw [(theta_congr_nhds he).eq_of_nhds]
  have hdf := hf.differentiableAt (by norm_num)
  have hdg := hg.differentiableAt (by norm_num)
  rw [theta_add ((differentiableAt_theta hf).mul hdg)
      (hdf.mul (differentiableAt_theta hg)),
    theta_mul (differentiableAt_theta hf) hdg,
    theta_mul hdf (differentiableAt_theta hg)]
  ring

noncomputable def rationalWeight (q : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ∏ a ∈ Icc 1 K, (1 - q ^ a * x)⁻¹

noncomputable def weightAlpha (q : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ Icc 1 K, q ^ a * x / (1 - q ^ a * x)

noncomputable def weightBeta (q : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ Icc 1 K, q ^ a * x / (1 - q ^ a * x) ^ 2

theorem one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (v : ι → ℝ)
    (hv0 : ∀ i ∈ s, 0 ≤ v i) (hv1 : ∀ i ∈ s, v i ≤ 1) :
    1 - ∑ i ∈ s, v i ≤ ∏ i ∈ s, (1 - v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hvi0 := hv0 i (mem_insert_self i s)
    have hvi1 := hv1 i (mem_insert_self i s)
    have hvs0 : ∀ j ∈ s, 0 ≤ v j := fun j hj => hv0 j (mem_insert_of_mem hj)
    have hvs1 : ∀ j ∈ s, v j ≤ 1 := fun j hj => hv1 j (mem_insert_of_mem hj)
    have h := mul_le_mul_of_nonneg_left (ih hvs0 hvs1) (sub_nonneg.mpr hvi1)
    have hs : 0 ≤ ∑ j ∈ s, v j := sum_nonneg hvs0
    rw [sum_insert hi, prod_insert hi]
    nlinarith [mul_nonneg hs hvi0]

theorem sum_geometric_nodes_le_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) (K : ℕ) :
    ∑ a ∈ Icc 1 K, q ^ a ≤ 1 := by
  calc _ ≤ ∑ a ∈ Icc 1 K, (1 / 2 : ℝ) ^ a :=
      sum_le_sum fun a _ => pow_le_pow_left₀ hq0 hq1 a
    _ ≤ 1 := sum_half_pow_le K

theorem weight_factor_bounds {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hx0 : 0 ≤ x) (hxq : x ≤ q) {a : ℕ} (ha : 1 ≤ a) :
    0 ≤ q ^ a * x ∧ q ^ a * x ≤ 1 / 4 := by
  have hqa : q ^ a ≤ q := by
    simpa using pow_le_pow_of_le_one hq0 (by linarith : q ≤ 1) ha
  have hpow0 := pow_nonneg hq0 a
  constructor
  · positivity
  · nlinarith [mul_le_mul hqa hxq hx0 hq0]

theorem rationalWeight_bounds {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hx0 : 0 ≤ x) (hxq : x ≤ q) (K : ℕ) :
    0 < rationalWeight q K x ∧ rationalWeight q K x ≤ 2 := by
  have hfac : ∀ a ∈ Icc 1 K, 0 < 1 - q ^ a * x := by
    intro a ha
    have h := weight_factor_bounds hq0 hq1 hx0 hxq (mem_Icc.mp ha).1
    linarith
  have hprod : 1 / 2 ≤ ∏ a ∈ Icc 1 K, (1 - q ^ a * x) := by
    have h := one_sub_sum_le_prod (Icc 1 K) (fun a => q ^ a * x)
      (fun a ha => (weight_factor_bounds hq0 hq1 hx0 hxq (mem_Icc.mp ha).1).1)
      (fun a ha => le_trans (weight_factor_bounds hq0 hq1 hx0 hxq (mem_Icc.mp ha).1).2 (by norm_num))
    rw [← sum_mul] at h
    have hsum := sum_geometric_nodes_le_one hq0 hq1 K
    nlinarith [mul_le_mul_of_nonneg_right hsum hx0]
  unfold rationalWeight
  rw [Finset.prod_inv_distrib]
  constructor
  · exact inv_pos.mpr (prod_pos hfac)
  · rw [inv_le_iff_one_le_mul₀ (prod_pos hfac)]
    linarith

theorem contDiffAt_rationalWeight {q x : ℝ} (K : ℕ)
    (hx : ∀ a ∈ Icc 1 K, 1 - q ^ a * x ≠ 0) :
    ContDiffAt ℝ 2 (rationalWeight q K) x := by
  apply contDiffAt_prod
  intro a ha
  exact (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)).inv (hx a ha)

theorem contDiffAt_weightAlpha {q x : ℝ} (K : ℕ)
    (hx : ∀ a ∈ Icc 1 K, 1 - q ^ a * x ≠ 0) :
    ContDiffAt ℝ 2 (weightAlpha q K) x := by
  apply ContDiffAt.sum
  intro a ha
  exact (contDiffAt_const.mul contDiffAt_id).div
    (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)) (hx a ha)

theorem hasDerivAt_weight_factor {q x : ℝ} (a : ℕ) (hx : 1 - q ^ a * x ≠ 0) :
    HasDerivAt (fun y : ℝ => (1 - q ^ a * y)⁻¹) (q ^ a / (1 - q ^ a * x) ^ 2) x := by
  convert ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).const_mul (q ^ a))).inv hx using 1
  · rfl
  · simp

theorem theta_rationalWeight {q x : ℝ} (K : ℕ)
    (hx : ∀ a ∈ Icc 1 K, 1 - q ^ a * x ≠ 0) :
    theta (rationalWeight q K) x = rationalWeight q K x * weightAlpha q K x := by
  have hd := HasDerivAt.fun_finsetProd
    (fun a ha => hasDerivAt_weight_factor a (hx a ha))
  change x * deriv (fun y => ∏ a ∈ Icc 1 K, (1 - q ^ a * y)⁻¹) x = _
  rw [hd.deriv]
  simp only [smul_eq_mul, Finset.mul_sum, weightAlpha, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hw : rationalWeight q K x =
      (1 - q ^ a * x)⁻¹ * ∏ b ∈ (Icc 1 K).erase a, (1 - q ^ b * x)⁻¹ := by
    exact (Finset.mul_prod_erase _ _ ha).symm
  rw [hw]
  field_simp

theorem theta_weightAlpha {q x : ℝ} (K : ℕ)
    (hx : ∀ a ∈ Icc 1 K, 1 - q ^ a * x ≠ 0) :
    theta (weightAlpha q K) x = weightBeta q K x := by
  have hd (a : ℕ) (ha : a ∈ Icc 1 K) :
      HasDerivAt (fun y : ℝ => q ^ a * y / (1 - q ^ a * y))
        (q ^ a / (1 - q ^ a * x) ^ 2) x := by
    convert ((hasDerivAt_id x).const_mul (q ^ a)).div
      ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).const_mul (q ^ a))) (hx a ha) using 1
    · rfl
    · dsimp
      ring
  change x * deriv (fun y => ∑ a ∈ Icc 1 K, q ^ a * y / (1 - q ^ a * y)) x = _
  rw [(HasDerivAt.fun_sum hd).deriv]
  simp only [weightBeta, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem theta_sq_rationalWeight {q x : ℝ} (K : ℕ)
    (hx : ∀ a ∈ Icc 1 K, 1 - q ^ a * x ≠ 0) :
    theta (theta (rationalWeight q K)) x =
      rationalWeight q K x * (weightAlpha q K x ^ 2 + weightBeta q K x) := by
  have hgood : ∀ᶠ y in 𝓝 x, ∀ a ∈ Icc 1 K, 1 - q ^ a * y ≠ 0 := by
    rw [Finset.eventually_all]
    intro a ha
    exact (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).eventually_ne (hx a ha)
  have he : theta (rationalWeight q K) =ᶠ[𝓝 x] rationalWeight q K * weightAlpha q K :=
    hgood.mono (fun y hy => theta_rationalWeight K hy)
  rw [(theta_congr_nhds he).eq_of_nhds,
    theta_mul ((contDiffAt_rationalWeight K hx).differentiableAt (by norm_num))
      ((contDiffAt_weightAlpha K hx).differentiableAt (by norm_num)),
    theta_rationalWeight K hx, theta_weightAlpha K hx]
  ring

theorem weightAlpha_bounds {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hx0 : 0 ≤ x) (hxq : x ≤ q) (K : ℕ) :
    0 ≤ weightAlpha q K x ∧ weightAlpha q K x ≤ (4 / 3) * x := by
  have hterm (a : ℕ) (ha : a ∈ Icc 1 K) :
      0 ≤ q ^ a * x / (1 - q ^ a * x) ∧
      q ^ a * x / (1 - q ^ a * x) ≤ (4 / 3) * (q ^ a * x) := by
    have hy := weight_factor_bounds hq0 hq1 hx0 hxq (mem_Icc.mp ha).1
    constructor
    · exact div_nonneg hy.1 (by linarith)
    · calc
        _ ≤ (q ^ a * x) / (3 / 4) :=
          div_le_div_of_nonneg_left hy.1 (by norm_num) (by linarith)
        _ = _ := by ring
  constructor
  · exact sum_nonneg (fun a ha => (hterm a ha).1)
  · calc
      weightAlpha q K x ≤ ∑ a ∈ Icc 1 K, (4 / 3) * (q ^ a * x) :=
        sum_le_sum (fun a ha => (hterm a ha).2)
      _ = (4 / 3) * (∑ a ∈ Icc 1 K, q ^ a) * x := by rw [← mul_sum, ← sum_mul]; ring
      _ ≤ (4 / 3) * x := by
        have h := mul_le_mul_of_nonneg_right (sum_geometric_nodes_le_one hq0 hq1 K) hx0
        nlinarith

theorem weightBeta_bounds {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hx0 : 0 ≤ x) (hxq : x ≤ q) (K : ℕ) :
    0 ≤ weightBeta q K x ∧ weightBeta q K x ≤ (16 / 9) * x := by
  have hterm (a : ℕ) (ha : a ∈ Icc 1 K) :
      0 ≤ q ^ a * x / (1 - q ^ a * x) ^ 2 ∧
      q ^ a * x / (1 - q ^ a * x) ^ 2 ≤ (16 / 9) * (q ^ a * x) := by
    have hy := weight_factor_bounds hq0 hq1 hx0 hxq (mem_Icc.mp ha).1
    constructor
    · exact div_nonneg hy.1 (sq_nonneg _)
    · calc
        _ ≤ (q ^ a * x) / (9 / 16) :=
          div_le_div_of_nonneg_left hy.1 (by norm_num) (by nlinarith [sq_nonneg (q ^ a * x - 1 / 4)])
        _ = _ := by ring
  constructor
  · exact sum_nonneg (fun a ha => (hterm a ha).1)
  · calc
      weightBeta q K x ≤ ∑ a ∈ Icc 1 K, (16 / 9) * (q ^ a * x) :=
        sum_le_sum (fun a ha => (hterm a ha).2)
      _ = (16 / 9) * (∑ a ∈ Icc 1 K, q ^ a) * x := by rw [← mul_sum, ← sum_mul]; ring
      _ ≤ (16 / 9) * x := by
        have h := mul_le_mul_of_nonneg_right (sum_geometric_nodes_le_one hq0 hq1 K) hx0
        nlinarith

/-- Uniform bounds for the weight and both Euler derivatives on `0 ≤ x ≤ q ≤ 1/2`. -/
theorem rationalWeight_euler_bounds {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hx0 : 0 ≤ x) (hxq : x ≤ q) (K : ℕ) :
    |rationalWeight q K x| ≤ 2 ∧
      |theta (rationalWeight q K) x| ≤ (8 / 3) * x ∧
      |theta (theta (rationalWeight q K)) x| ≤ (16 / 3) * x := by
  have hw := rationalWeight_bounds hq0 hq1 hx0 hxq K
  have ha := weightAlpha_bounds hq0 hq1 hx0 hxq K
  have hb := weightBeta_bounds hq0 hq1 hx0 hxq K
  have hx : ∀ a ∈ Icc 1 K, 1 - q ^ a * x ≠ 0 := by
    intro a ha
    have hy := weight_factor_bounds hq0 hq1 hx0 hxq (mem_Icc.mp ha).1
    linarith
  rw [abs_of_pos hw.1, theta_rationalWeight K hx, theta_sq_rationalWeight K hx,
    abs_of_nonneg (mul_nonneg hw.1.le ha.1),
    abs_of_nonneg (mul_nonneg hw.1.le (add_nonneg (sq_nonneg _) hb.1))]
  refine ⟨hw.2, ?_, ?_⟩
  · calc _ ≤ 2 * ((4 / 3) * x) := mul_le_mul hw.2 ha.2 ha.1 (by norm_num)
         _ = _ := by ring
  · have hasq : weightAlpha q K x ^ 2 ≤ (8 / 9) * x := by
      have h := mul_self_le_mul_self ha.1 ha.2
      have hxhalf : x ≤ 1 / 2 := le_trans hxq hq1
      nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hxhalf)]
    have hab : weightAlpha q K x ^ 2 + weightBeta q K x ≤ (8 / 3) * x := by linarith
    calc _ ≤ 2 * ((8 / 3) * x) :=
          mul_le_mul hw.2 hab (add_nonneg (sq_nonneg _) hb.1) (by norm_num)
         _ = _ := by ring

end QZeta3
