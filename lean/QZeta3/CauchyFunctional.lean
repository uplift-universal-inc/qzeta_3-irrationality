import QZeta3.GramIdentity
import QZeta3.CauchyAtInfinity

open Finset Filter Topology

namespace QZeta3

/-- The Cauchy transform `𝓕(z) = ∑_{m ≥ 1} q^m (z + q^m)/(z − q^m)³`, `q = 1/p` (eq. (5.1)). -/
noncomputable def cauchyF (p : ℕ) (z : ℝ) : ℝ :=
  ∑' m : ℕ, ((p : ℝ)⁻¹) ^ (m + 1) * (z + ((p : ℝ)⁻¹) ^ (m + 1)) / (z - ((p : ℝ)⁻¹) ^ (m + 1)) ^ 3

theorem deriv_inv_sub (z x : ℝ) (hx : x ≠ z) :
    deriv (fun y : ℝ => (z - y)⁻¹) x = ((z - x) ^ 2)⁻¹ := by
  have hzx : z - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have h1 : HasDerivAt (fun y : ℝ => z - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub z
  have h2 : HasDerivAt (fun y : ℝ => (z - y)⁻¹) (-(-1) / (z - x) ^ 2) x := h1.inv hzx
  rw [h2.deriv]
  field_simp

/-- `θ²((z − x)⁻¹) = x(z + x)/(z − x)³` away from `x = z` (the computation behind eq. (5.1)). -/
theorem theta_theta_inv_sub (z x : ℝ) (hx : x ≠ z) :
    theta (theta (fun y : ℝ => (z - y)⁻¹)) x = x * (z + x) / (z - x) ^ 3 := by
  have hzx : z - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hev : (theta fun y : ℝ => (z - y)⁻¹) =ᶠ[nhds x] fun y => y * ((z - y) ^ 2)⁻¹ := by
    have hopen : {y : ℝ | y ≠ z} ∈ nhds x := isOpen_ne.mem_nhds hx
    filter_upwards [hopen] with y hy
    simp only [theta]
    rw [deriv_inv_sub z y hy]
  rw [show theta (theta fun y : ℝ => (z - y)⁻¹) x = x * deriv (theta fun y : ℝ => (z - y)⁻¹) x
    from rfl, hev.deriv_eq]
  have h1 : HasDerivAt (fun y : ℝ => z - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub z
  have h2 : HasDerivAt (fun y : ℝ => ((z - y) ^ 2)⁻¹)
      (-(((2 : ℕ) : ℝ) * (z - x) ^ (2 - 1) * -1) / ((z - x) ^ 2) ^ 2) x :=
    (h1.pow 2).inv (pow_ne_zero 2 hzx)
  have h3 : HasDerivAt (fun y : ℝ => y * ((z - y) ^ 2)⁻¹)
      (1 * ((z - x) ^ 2)⁻¹ + x * (-(((2 : ℕ) : ℝ) * (z - x) ^ (2 - 1) * -1) / ((z - x) ^ 2) ^ 2)) x :=
    (hasDerivAt_id x).mul h2
  rw [h3.deriv]
  field_simp
  ring

/-- `𝓕 = L((z − x)⁻¹)` for `z` outside the support. -/
theorem cauchyF_eq (p : ℕ) (z : ℝ) (hz : ∀ m : ℕ, z ≠ ((p : ℝ)⁻¹) ^ (m + 1)) :
    cauchyF p z = Lfun p (fun x => (z - x)⁻¹) := by
  unfold cauchyF Lfun
  refine tsum_congr fun m => ?_
  rw [theta_theta_inv_sub z _ (Ne.symm (hz m))]

end QZeta3
