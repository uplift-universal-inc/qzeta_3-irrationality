import QZeta3.Elementary
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Polynomial Finset Filter Topology

namespace QZeta3

/-- The Euler derivative. -/
noncomputable def theta (f : ℝ → ℝ) : ℝ → ℝ := fun x => x * deriv f x

/-- The functional evaluated on the positive geometric lattice. -/
noncomputable def Lfun (p : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑' m : ℕ, theta (theta f) (((p : ℝ)⁻¹) ^ (m + 1))

theorem theta_inv_affine {c x : ℝ} (hx : 1 - c * x ≠ 0) :
    theta (fun y => (1 - c * y)⁻¹) x = c * x / (1 - c * x)^2 := by
  have h := ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).const_mul c)).inv hx
  change HasDerivAt (fun y => (1 - c * y)⁻¹) _ x at h
  rw [theta, h.deriv]
  simp only [Pi.sub_apply, id_eq]
  ring

theorem theta_sq_inv_affine {c x : ℝ} (hx : 1 - c * x ≠ 0) :
    theta (theta (fun y => (1 - c * y)⁻¹)) x =
      (c * x) * (1 + c * x) / (1 - c * x)^3 := by
  have he : theta (fun y => (1 - c * y)⁻¹) =ᶠ[𝓝 x]
      (fun y => c * y / (1 - c * y)^2) := by
    have hn : ∀ᶠ y in 𝓝 x, 1 - c * y ≠ 0 :=
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually_ne hx
    exact hn.mono fun y hy => theta_inv_affine hy
  have h := ((hasDerivAt_id x).const_mul c).div
    (((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).const_mul c)).pow 2)
    (pow_ne_zero 2 hx)
  change HasDerivAt (fun y => c * y / (1 - c * y)^2) _ x at h
  change x * deriv (theta (fun y => (1 - c * y)⁻¹)) x = _
  rw [he.deriv_eq, h.deriv]
  simp only [Pi.pow_apply, Pi.sub_apply, id_eq, Nat.cast_ofNat]
  norm_num only [Nat.reduceSub, pow_one, zero_sub, mul_one]
  simp only [pow_two, div_eq_mul_inv]
  field_simp [hx]
  ring

/-- The rational kernel obtained by differentiating a simple pole twice. -/
noncomputable def poleKernel (p b : ℕ) : ℝ :=
  ((p : ℝ)⁻¹)^b * (1 + ((p : ℝ)⁻¹)^b) / (1 - ((p : ℝ)⁻¹)^b)^3

theorem inv_base_pos {p : ℕ} (hp : 2 ≤ p) : 0 < (p : ℝ)⁻¹ := by
  have : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  positivity

theorem inv_base_lt_one {p : ℕ} (hp : 2 ≤ p) : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast (show 1 < p by omega))

theorem inv_base_pow_lt_one {p b : ℕ} (hp : 2 ≤ p) (hb : 0 < b) :
    ((p : ℝ)⁻¹)^b < 1 :=
  pow_lt_one₀ (le_of_lt (inv_base_pos hp)) (inv_base_lt_one hp) (Nat.ne_of_gt hb)

theorem hasSum_geometric_lattice_row {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    HasSum (fun m : ℕ => ((n + 1 : ℕ) : ℝ)^2 *
      ((p : ℝ)⁻¹)^((n + 1) * (m + 1))) (term p (n + 1)) := by
  have h := (hasSum_geometric_of_lt_one
    (pow_nonneg (le_of_lt (inv_base_pos hp)) (n + 1))
    (inv_base_pow_lt_one hp (by omega))).mul_left
    (((n + 1 : ℕ) : ℝ)^2 * ((p : ℝ)⁻¹)^(n + 1))
  convert h using 1
  · ext m
    rw [Nat.mul_add, pow_add, pow_mul]
    ring
  · unfold term
    have hpn : (p : ℝ)^(n + 1) ≠ 0 := by
      exact ne_of_gt (lt_trans zero_lt_one (one_lt_pow_succ hp n))
    have hpn1 : (p : ℝ)^(n + 1) - 1 ≠ 0 := by
      exact ne_of_gt (sub_pos.mpr (one_lt_pow_succ hp n))
    rw [inv_pow]
    field_simp

theorem hasSum_geometric_lattice_column {p : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ)^2 *
      ((p : ℝ)⁻¹)^((n + 1) * (m + 1))) (poleKernel p (m + 1)) := by
  have hr : ‖((p : ℝ)⁻¹)^(m + 1)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_of_lt (inv_base_pos hp)) _)]
    exact inv_base_pow_lt_one hp (by omega)
  have hs := hasSum_sq_mul_geometric_of_norm_lt_one hr
  have hshift : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ)^2 *
      (((p : ℝ)⁻¹)^(m + 1))^(n + 1)) (poleKernel p (m + 1)) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℝ)^2 *
      (((p : ℝ)⁻¹)^(m + 1))^n) 1).mpr
    simpa [poleKernel] using hs
  convert hshift using 1
  ext n
  rw [← pow_mul, Nat.mul_comm]

/-- Tonelli's theorem identifies the sum of the differentiated geometric kernels with ξ. -/
theorem hasSum_poleKernel {p : ℕ} (hp : 2 ≤ p) :
    HasSum (fun m : ℕ => poleKernel p (m + 1)) (xi p) := by
  let f : ℕ × ℕ → ℝ := fun nm => ((nm.1 + 1 : ℕ) : ℝ)^2 *
    ((p : ℝ)⁻¹)^((nm.1 + 1) * (nm.2 + 1))
  have hf : Summable f := by
    apply (summable_prod_of_nonneg (fun nm => by dsimp [f]; positivity)).mpr
    constructor
    · intro n
      exact (hasSum_geometric_lattice_row hp n).summable
    · convert summable_term hp using 1
      ext n
      exact (hasSum_geometric_lattice_row hp n).tsum_eq
  have heq : (fun m : ℕ => ∑' n : ℕ, f (n, m)) =
      (fun m : ℕ => poleKernel p (m + 1)) := by
    funext m
    exact (hasSum_geometric_lattice_column hp m).tsum_eq
  have hsum : Summable (fun m : ℕ => poleKernel p (m + 1)) := by
    rw [← heq]
    exact hf.prod_symm.prod
  convert hsum.hasSum using 1
  have hcomm := Summable.tsum_comm (f := fun n m : ℕ => f (n, m)) hf
  rw [← heq, hcomm]
  unfold xi
  congr 1
  funext n
  exact (hasSum_geometric_lattice_row hp n).tsum_eq.symm

theorem S_cast_eq_sum_poleKernel {p : ℕ} (hp : 2 ≤ p) (a : ℕ) :
    (S p a : ℝ) = ∑ m ∈ range a, poleKernel p (m + 1) := by
  have hI : (S p a : ℝ) = ∑ b ∈ Icc 1 a, poleKernel p b := by
    rw [S_eq_sum_g hp]
    simp only [Rat.cast_sum, g, poleKernel, Rat.cast_div, Rat.cast_mul,
      Rat.cast_add, Rat.cast_sub, Rat.cast_pow, Rat.cast_inv, Rat.cast_one,
      Rat.cast_natCast, inv_pow]
  rw [hI]
  clear hI
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_Icc_succ_top (by omega), sum_range_succ, ih]

/-- The value of a simple pole is the tail of the kernel sum. -/
theorem Lfun_simplePole_eq_tail {p : ℕ} (hp : 2 ≤ p) (a : ℕ) :
    Lfun p (fun x => (1 - ((p : ℝ)⁻¹)^a * x)⁻¹) =
      ∑' m : ℕ, poleKernel p (m + a + 1) := by
  unfold Lfun
  apply tsum_congr
  intro m
  have hlt : ((p : ℝ)⁻¹)^a * ((p : ℝ)⁻¹)^(m + 1) < 1 := by
    rw [← pow_add]
    exact inv_base_pow_lt_one hp (by omega)
  rw [theta_sq_inv_affine (by linarith :
    1 - ((p : ℝ)⁻¹)^a * ((p : ℝ)⁻¹)^(m + 1) ≠ 0)]
  unfold poleKernel
  have he : a + (m + 1) = m + a + 1 := by omega
  simp only [← pow_add, he]

/-- Pure simple-pole moments (Lemma 1.2), with all series summability established. -/
theorem purity {p : ℕ} (hp : 2 ≤ p) (a : ℕ) (_ha : 1 ≤ a) :
    Lfun p (fun x => (1 - ((p : ℝ)⁻¹)^a * x)⁻¹) = xi p - (S p a : ℝ) := by
  rw [Lfun_simplePole_eq_tail hp, S_cast_eq_sum_poleKernel hp]
  have h := (hasSum_poleKernel hp).summable.sum_add_tsum_nat_add a
  rw [(hasSum_poleKernel hp).tsum_eq] at h
  linarith

theorem theta_pow (j : ℕ) : theta (fun x : ℝ => x^j) = (fun x => (j : ℝ) * x^j) := by
  funext x
  unfold theta
  rw [(hasDerivAt_pow j x).deriv]
  cases j with
  | zero => simp
  | succ j => simp only [Nat.add_sub_cancel, pow_succ]; ring

theorem theta_sq_pow (j : ℕ) :
    theta (theta (fun x : ℝ => x^j)) = (fun x => (j : ℝ)^2 * x^j) := by
  rw [theta_pow]
  funext x
  unfold theta
  rw [((hasDerivAt_pow j x).const_mul (j : ℝ)).deriv]
  cases j with
  | zero => simp
  | succ j => simp only [Nat.add_sub_cancel, pow_succ]; ring

/-- The monomial moment series converges to its prescribed rational value. -/
theorem hasSum_monomial {p : ℕ} (hp : 2 ≤ p) (j : ℕ) :
    HasSum (fun m : ℕ => theta (theta (fun x : ℝ => x^j))
      (((p : ℝ)⁻¹)^(m + 1))) (mu p j : ℝ) := by
  rw [theta_sq_pow]
  cases j with
  | zero => simpa [mu] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  | succ j =>
    convert hasSum_geometric_lattice_row hp j using 1
    · ext m
      dsimp only
      rw [← pow_mul, Nat.mul_comm]
    · simp [mu, term]

/-- The polynomial moments `L(x^j) = μ_j`, including the constant case. -/
theorem Lfun_pow {p : ℕ} (hp : 2 ≤ p) (j : ℕ) :
    Lfun p (fun x : ℝ => x^j) = (mu p j : ℝ) :=
  (hasSum_monomial hp j).tsum_eq

end QZeta3
