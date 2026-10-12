import QZeta3.AnalyticWeight
import QZeta3.GramIdentity

/-! # A bound uniform in the moving denominator for all monomial moments. -/

open Finset Filter Topology

namespace QZeta3

theorem rationalWeight_eq_inv_DK (p K : ℕ) :
    rationalWeight ((p : ℝ)⁻¹) K = (fun x => (DK p K x)⁻¹) := by
  funext x
  simp only [rationalWeight, DK, Finset.prod_inv_distrib]

theorem fraction_DK_eq_mul_weight (p K k : ℕ) :
    (fun x : ℝ => x ^ k / DK p K x) =
      (fun x => x ^ k) * rationalWeight ((p : ℝ)⁻¹) K := by
  rw [rationalWeight_eq_inv_DK]
  rfl

theorem theta_sq_monomial_weight_bound {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hx0 : 0 ≤ x) (hxq : x ≤ q) (K k : ℕ) :
    |theta (theta ((fun y : ℝ => y ^ k) * rationalWeight q K)) x| ≤
      8 * ((k : ℝ) + 1) ^ 2 * x ^ k := by
  have hfac : ∀ a ∈ Icc 1 K, 1 - q ^ a * x ≠ 0 := by
    intro a ha
    have h := weight_factor_bounds hq0 hq1 hx0 hxq (mem_Icc.mp ha).1
    linarith
  have hw := rationalWeight_euler_bounds hq0 hq1 hx0 hxq K
  have hw1 : |theta (rationalWeight q K) x| ≤ 4 / 3 := by linarith [hw.2.1]
  have hw2 : |theta (theta (rationalWeight q K)) x| ≤ 8 / 3 := by linarith [hw.2.2]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hxk : 0 ≤ x ^ k := pow_nonneg hx0 k
  have hcd : ContDiffAt ℝ 2 (fun y : ℝ => y ^ k) x := contDiffAt_id.pow k
  rw [theta_sq_mul hcd (contDiffAt_rationalWeight K hfac),
    theta_sq_pow, theta_pow]
  dsimp only
  calc
    _ ≤ |(k : ℝ) ^ 2 * x ^ k * rationalWeight q K x| +
        |2 * ((k : ℝ) * x ^ k) * theta (rationalWeight q K) x| +
        |x ^ k * theta (theta (rationalWeight q K)) x| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = (k : ℝ) ^ 2 * x ^ k * |rationalWeight q K x| +
        2 * ((k : ℝ) * x ^ k) * |theta (rationalWeight q K) x| +
        x ^ k * |theta (theta (rationalWeight q K)) x| := by
      simp only [abs_mul, abs_of_nonneg hk0, abs_of_nonneg hxk, abs_of_nonneg (sq_nonneg (k : ℝ)),
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (k : ℝ) ^ 2 * x ^ k * 2 + 2 * ((k : ℝ) * x ^ k) * (4 / 3) +
        x ^ k * (8 / 3) := by gcongr; exact hw.1
    _ = (2 * (k : ℝ) ^ 2 + (8 / 3) * k + 8 / 3) * x ^ k := by ring
    _ ≤ 8 * ((k : ℝ) + 1) ^ 2 * x ^ k := by
      apply mul_le_mul_of_nonneg_right _ hxk
      nlinarith

theorem abs_tsum_le_of_majorant {f g : ℕ → ℝ} {B : ℝ}
    (hg : HasSum g B) (hfg : ∀ m, |f m| ≤ g m) : |∑' m, f m| ≤ B := by
  have hf : Summable (fun m => |f m|) :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) hfg hg.summable
  calc
    _ ≤ ∑' m, |f m| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := f) (by simpa only [Real.norm_eq_abs] using hf)
    _ ≤ ∑' m, g m := hf.tsum_mono hg.summable hfg
    _ = B := hg.tsum_eq

theorem hasSum_geometric_shift {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun m : ℕ => q ^ (m + 1)) (q / (1 - q)) := by
  convert (hasSum_geometric_of_lt_one hq0 hq1).mul_left q using 1
  · funext m
    rw [pow_succ]
    ring
  · rw [div_eq_mul_inv]

theorem Lfun_monomial_weight_bound {p : ℕ} (hp : 2 ≤ p) (K k : ℕ) :
    |Lfun p (fun x : ℝ => x ^ k / DK p K x)| ≤
      16 * ((k : ℝ) + 1) ^ 2 * ((p : ℝ)⁻¹) ^ k := by
  let q : ℝ := (p : ℝ)⁻¹
  have hq0 : 0 < q := inv_base_pos hp
  have hq1 : q ≤ 1 / 2 := by
    apply (inv_le_iff_one_le_mul₀ (by exact_mod_cast (show 0 < p by omega))).mpr
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hx0 (m : ℕ) : 0 ≤ q ^ (m + 1) := pow_nonneg hq0.le _
  have hxq (m : ℕ) : q ^ (m + 1) ≤ q := by
    simpa using pow_le_pow_of_le_one hq0.le (by linarith : q ≤ 1) (show 1 ≤ m + 1 by omega)
  rw [fraction_DK_eq_mul_weight]
  change |∑' m : ℕ, theta (theta ((fun x : ℝ => x ^ k) * rationalWeight q K))
    (q ^ (m + 1))| ≤ 16 * ((k : ℝ) + 1) ^ 2 * q ^ k
  by_cases hk : k = 0
  · subst k
    have he : (fun x : ℝ => x ^ 0) * rationalWeight q K = rationalWeight q K := by
      funext x
      simp
    rw [he]
    have h := abs_tsum_le_of_majorant ((hasSum_geometric_shift hq0.le (by linarith)).mul_left
      (16 / 3)) (fun m => (rationalWeight_euler_bounds hq0.le hq1 (hx0 m) (hxq m) K).2.2)
    have hfrac : q / (1 - q) ≤ 1 := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - q)).mpr
      linarith
    simpa using h.trans (show (16 / 3) * (q / (1 - q)) ≤ 16 * ((0 : ℝ) + 1) ^ 2 * q ^ 0 by
      nlinarith)
  · have hqk : q ^ k ≤ 1 / 2 := by
      have hpow : q ^ k ≤ q := by
        simpa using pow_le_pow_of_le_one hq0.le (by linarith : q ≤ 1) (show 1 ≤ k by omega)
      exact hpow.trans hq1
    have hs := (hasSum_geometric_shift (pow_nonneg hq0.le k) (by linarith : q ^ k < 1)).mul_left
      (8 * ((k : ℝ) + 1) ^ 2)
    have hs' : HasSum (fun m : ℕ => 8 * ((k : ℝ) + 1) ^ 2 * (q ^ (m + 1)) ^ k)
        (8 * ((k : ℝ) + 1) ^ 2 * (q ^ k / (1 - q ^ k))) := by
      convert hs using 1
      funext m
      rw [← pow_mul, ← pow_mul, Nat.mul_comm k (m + 1)]
    have h := abs_tsum_le_of_majorant hs'
      (fun m => theta_sq_monomial_weight_bound hq0.le hq1 (hx0 m) (hxq m) K k)
    have hfrac : q ^ k / (1 - q ^ k) ≤ 2 * q ^ k := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - q ^ k)).mpr
      nlinarith [mul_nonneg (pow_nonneg hq0.le k) (sub_nonneg.mpr hqk)]
    calc _ ≤ 8 * ((k : ℝ) + 1) ^ 2 * (q ^ k / (1 - q ^ k)) := h
         _ ≤ 8 * ((k : ℝ) + 1) ^ 2 * (2 * q ^ k) := by gcongr
         _ = _ := by ring

end QZeta3
