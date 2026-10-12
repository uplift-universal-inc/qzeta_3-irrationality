import QZeta3.AnalyticDeterminant
import QZeta3.AnalyticWeight
import QZeta3.GramIdentity
import QZeta3.GramBasis
import QZeta3.GeometricTail

/-! Pointwise and summed entry estimates in the triple-root basis. -/

open Polynomial Finset Filter Topology

namespace QZeta3

/-- Multiplication of two bounded Euler-jet triples. -/
theorem euler_product_estimate (a b u v U V A B i j t : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hi : 0 ≤ i) (hj : 0 ≤ j)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : |a| ≤ A) (hb : |b| ≤ B)
    (hu : |u| ≤ i * A * t) (hv : |v| ≤ j * B * t)
    (hU : |U| ≤ i ^ 2 * A * t) (hV : |V| ≤ j ^ 2 * B * t) :
    |a * b| ≤ A * B ∧
      |u * b + a * v| ≤ (i + j) * (A * B) * t ∧
      |U * b + 2 * u * v + a * V| ≤ (i + j) ^ 2 * (A * B) * t := by
  have hab : |a * b| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) hA
  have h₁ : |u * b + a * v| ≤ (i + j) * (A * B) * t := by
    calc _ ≤ |u * b| + |a * v| := abs_add_le _ _
      _ = |u| * |b| + |a| * |v| := by rw [abs_mul, abs_mul]
      _ ≤ (i * A * t) * B + A * (j * B * t) :=
        add_le_add (mul_le_mul hu hb (abs_nonneg _) (by positivity))
          (mul_le_mul ha hv (abs_nonneg _) hA)
      _ = _ := by ring
  have ht : t ^ 2 ≤ t := by nlinarith
  have h₂ : |U * b + 2 * u * v + a * V| ≤ (i + j) ^ 2 * (A * B) * t := by
    calc _ ≤ |U * b| + |2 * u * v| + |a * V| := abs_add_three _ _ _
      _ = |U| * |b| + 2 * |u| * |v| + |a| * |V| := by
        simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      _ ≤ (i ^ 2 * A * t) * B + 2 * (i * A * t) * (j * B * t) +
          A * (j ^ 2 * B * t) := by
        apply add_le_add
        · apply add_le_add (mul_le_mul hU hb (abs_nonneg _) (by positivity))
          exact mul_le_mul (mul_le_mul_of_nonneg_left hu (by norm_num)) hv
            (abs_nonneg _) (by positivity)
        · exact mul_le_mul ha hV (abs_nonneg _) hA
      _ = (i ^ 2 + j ^ 2) * (A * B) * t + (2 * i * j * A * B) * t ^ 2 := by ring
      _ ≤ (i ^ 2 + j ^ 2) * (A * B) * t + (2 * i * j * A * B) * t :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left ht (by positivity))
      _ = _ := by ring
  exact ⟨hab, h₁, h₂⟩

/-- Adjoining the rational weight preserves geometric decay of a jet. -/
theorem euler_weight_estimate (a u U w v V A h x t : ℝ)
    (hA : 0 ≤ A) (hh : 0 ≤ h) (_hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (ht : x ≤ t) (ht0 : 0 ≤ t)
    (ha : |a| ≤ A) (hu : |u| ≤ h * A * t) (hU : |U| ≤ h ^ 2 * A * t)
    (hw : |w| ≤ 2) (hv : |v| ≤ (8 / 3) * x) (hV : |V| ≤ (16 / 3) * x) :
    |U * w + 2 * u * v + a * V| ≤ (16 / 3) * (h + 1) ^ 2 * A * t := by
  calc _ ≤ |U * w| + |2 * u * v| + |a * V| := abs_add_three _ _ _
    _ = |U| * |w| + 2 * |u| * |v| + |a| * |V| := by
      simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    _ ≤ (h ^ 2 * A * t) * 2 + 2 * (h * A * t) * ((8 / 3) * x) + A * ((16 / 3) * x) := by
      apply add_le_add
      · apply add_le_add (mul_le_mul hU hw (abs_nonneg _) (by positivity))
        exact mul_le_mul (mul_le_mul_of_nonneg_left hu (by norm_num)) hv
          (abs_nonneg _) (by positivity)
      · exact mul_le_mul ha hV (abs_nonneg _) hA
    _ ≤ (h ^ 2 * A * t) * 2 + (16 / 3) * (h * A * t) + (16 / 3) * A * t := by
      have h₁ := mul_le_mul_of_nonneg_left hx1 (show 0 ≤ (16 / 3) * h * A * t by positivity)
      have h₂ := mul_le_mul_of_nonneg_left ht (show 0 ≤ (16 / 3) * A by positivity)
      nlinarith only [h₁, h₂]
    _ ≤ _ := by
      have hcoeff : 2 * h ^ 2 + (16 / 3) * h + (16 / 3) ≤ (16 / 3) * (h + 1) ^ 2 := by
        nlinarith [sq_nonneg h]
      nlinarith [mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hA ht0)]

theorem contDiffAt_realPolynomial (P : ℝ[X]) (x : ℝ) :
    ContDiffAt ℝ 2 (fun y => P.eval y) x := by
  simp only [eval_eq_sum, Polynomial.sum_def]
  exact ContDiffAt.sum fun j _ => contDiffAt_const.mul (contDiffAt_id.pow j)

theorem tripleRoot_jets_common {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (i m R : ℕ) (hi : (i + 2) / 3 ≤ R) (hm : R ≤ m) :
    |(tripleRootPoly q i).eval (q ^ m)| ≤ q ^ aj i ∧
      |theta (fun x => (tripleRootPoly q i).eval x) (q ^ m)| ≤
        (i : ℝ) * q ^ aj i * (q ^ m / q ^ R) ∧
      |theta (theta (fun x => (tripleRootPoly q i).eval x)) (q ^ m)| ≤
        (i : ℝ) ^ 2 * q ^ aj i * (q ^ m / q ^ R) := by
  have hxa := pow_le_pow_of_le_one hq.le hq1 hm
  have h := tripleRoot_derivative_bounds hq (pow_pos hq m).le (pow_pos hq _) hxa i
    (fun t ht => pow_le_pow_of_le_one hq.le hq1 (by
      have := (Finset.mem_Icc.mp ht).2
      omega))
  rw [theta_polynomial, theta_sq_polynomial]
  have he := euler_jet_bounds_of_derivative_bounds _ _ _ _ _ _
    (pow_pos hq m).le (pow_pos hq _) hxa h.2.1 h.2.2
  exact ⟨h.1, by simpa only [mul_div_assoc] using he⟩

theorem weight_eq_DK_inv (p K : ℕ) :
    rationalWeight ((p : ℝ)⁻¹) K = fun x => (DK p K x)⁻¹ := by
  funext x
  simp only [rationalWeight, DK, Finset.prod_inv_distrib]

/-- Pointwise decay of a transformed entry at a surviving lattice node. -/
theorem tripleRoot_entry_surviving {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (K i j m : ℕ) (hm : 1 ≤ m)
    (hR : max ((i + 2) / 3) ((j + 2) / 3) ≤ m) :
    |theta (theta (fun x => (tripleRootPoly q i).eval x *
        (tripleRootPoly q j).eval x * rationalWeight q K x)) (q ^ m)| ≤
      (16 / 3) * ((i : ℝ) + j + 1) ^ 2 * q ^ (aj i + aj j) *
        q ^ (m - max ((i + 2) / 3) ((j + 2) / 3)) := by
  let R := max ((i + 2) / 3) ((j + 2) / 3)
  let x := q ^ m
  let t := x / q ^ R
  let f : ℝ → ℝ := fun x => (tripleRootPoly q i).eval x
  let g : ℝ → ℝ := fun x => (tripleRootPoly q j).eval x
  have hq1 : q ≤ 1 := by linarith
  have hx0 : 0 ≤ x := (pow_pos hq m).le
  have hxq : x ≤ q := by simpa only [pow_one] using pow_le_pow_of_le_one hq.le hq1 hm
  have hx1 : x ≤ 1 := le_trans hxq hq1
  have ht0 : 0 ≤ t := div_nonneg hx0 (pow_pos hq R).le
  have ht1 : t ≤ 1 := (div_le_one (pow_pos hq R)).mpr (pow_le_pow_of_le_one hq.le hq1 hR)
  have hxt : x ≤ t := (le_div_iff₀ (pow_pos hq R)).mpr (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hq.le hq1) hx0)
  have hi := tripleRoot_jets_common hq hq1 i m R (le_max_left _ _) hR
  have hj := tripleRoot_jets_common hq hq1 j m R (le_max_right _ _) hR
  have hf := contDiffAt_realPolynomial (tripleRootPoly q i) x
  have hg := contDiffAt_realPolynomial (tripleRootPoly q j) x
  have hw : ContDiffAt ℝ 2 (rationalWeight q K) x :=
    contDiffAt_rationalWeight K (fun a ha => by
      have hy := weight_factor_bounds hq.le hqhalf hx0 hxq (mem_Icc.mp ha).1
      linarith)
  have hp := euler_product_estimate (f x) (g x) (theta f x) (theta g x)
    (theta (theta f) x) (theta (theta g) x) (q ^ aj i) (q ^ aj j) i j t
    (pow_pos hq _).le (pow_pos hq _).le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    ht0 ht1 hi.1 hj.1 hi.2.1 hj.2.1 hi.2.2 hj.2.2
  have hp0 : |(f * g) x| ≤ q ^ aj i * q ^ aj j := hp.1
  have hp1 : |theta (f * g) x| ≤ ((i : ℝ) + j) * (q ^ aj i * q ^ aj j) * t := by
    rw [theta_mul (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))]
    exact hp.2.1
  have hp2 : |theta (theta (f * g)) x| ≤ ((i : ℝ) + j) ^ 2 *
      (q ^ aj i * q ^ aj j) * t := by
    rw [theta_sq_mul hf hg]
    exact hp.2.2
  have hwbound := rationalWeight_euler_bounds hq.le hqhalf hx0 hxq K
  have h := euler_weight_estimate ((f * g) x) (theta (f * g) x)
    (theta (theta (f * g)) x) (rationalWeight q K x) (theta (rationalWeight q K) x)
    (theta (theta (rationalWeight q K)) x) (q ^ aj i * q ^ aj j) (i + j) x t
    (by positivity) (by positivity) hx0 hx1 hxt ht0 hp0 hp1 hp2
    hwbound.1 hwbound.2.1 hwbound.2.2
  have ht : t = q ^ (m - R) := by
    dsimp [t, x]
    exact (pow_sub₀ q hq.ne' hR).symm
  change |theta (theta ((f * g) * rationalWeight q K)) x| ≤ _
  rw [theta_sq_mul (f := f * g) (g := rationalWeight q K) (hf.mul hg) hw]
  simpa only [← pow_add, ht, R] using h

theorem euler_jets_mul_vanish_left {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (h₀ : f x = 0) (h₁ : theta f x = 0) (h₂ : theta (theta f) x = 0) :
    (f * g) x = 0 ∧ theta (f * g) x = 0 ∧ theta (theta (f * g)) x = 0 := by
  rw [theta_mul (f := f) (g := g) (hf.differentiableAt (by norm_num))
      (hg.differentiableAt (by norm_num)), theta_sq_mul hf hg]
  simp only [Pi.mul_apply, h₀, h₁, h₂, zero_mul, mul_zero, add_zero, and_self]

theorem euler_jets_mul_vanish_right {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (h₀ : g x = 0) (h₁ : theta g x = 0) (h₂ : theta (theta g) x = 0) :
    (f * g) x = 0 ∧ theta (f * g) x = 0 ∧ theta (theta (f * g)) x = 0 := by
  rw [mul_comm f g]
  exact euler_jets_mul_vanish_left hg hf h₀ h₁ h₂

/-- All earlier lattice nodes vanish, including the weighted second jet. -/
theorem tripleRoot_entry_vanish {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (K i j m : ℕ) (hm : 1 ≤ m)
    (hR : m < max ((i + 2) / 3) ((j + 2) / 3)) :
    theta (theta (fun x => (tripleRootPoly q i).eval x *
      (tripleRootPoly q j).eval x * rationalWeight q K x)) (q ^ m) = 0 := by
  let f : ℝ → ℝ := fun x => (tripleRootPoly q i).eval x
  let g : ℝ → ℝ := fun x => (tripleRootPoly q j).eval x
  have hf : ContDiffAt ℝ 2 f (q ^ m) := contDiffAt_realPolynomial _ _
  have hg : ContDiffAt ℝ 2 g (q ^ m) := contDiffAt_realPolynomial _ _
  have hq1 : q ≤ 1 := by linarith
  have hxq : q ^ m ≤ q := by
    simpa only [pow_one] using pow_le_pow_of_le_one hq.le hq1 hm
  have hw : ContDiffAt ℝ 2 (rationalWeight q K) (q ^ m) :=
    contDiffAt_rationalWeight K (fun a ha => by
      have hy := weight_factor_bounds hq.le hqhalf (pow_pos hq m).le hxq (mem_Icc.mp ha).1
      linarith)
  have hprod : (f * g) (q ^ m) = 0 ∧ theta (f * g) (q ^ m) = 0 ∧
      theta (theta (f * g)) (q ^ m) = 0 := by
    rcases lt_max_iff.mp hR with h | h
    · obtain ⟨h₀, h₁, h₂⟩ := tripleRoot_euler_vanish q hm h
      exact euler_jets_mul_vanish_left hf hg h₀ h₁ h₂
    · obtain ⟨h₀, h₁, h₂⟩ := tripleRoot_euler_vanish q hm h
      exact euler_jets_mul_vanish_right hf hg h₀ h₁ h₂
  exact (euler_jets_mul_vanish_left (f := f * g) (g := rationalWeight q K)
    (hf.mul hg) hw hprod.1 hprod.2.1 hprod.2.2).2.2

theorem inv_base_le_half {p : ℕ} (hp : 2 ≤ p) : (p : ℝ)⁻¹ ≤ 1 / 2 := by
  simpa only [one_div] using one_div_le_one_div_of_le
    (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hp : (2 : ℝ) ≤ p)

/-- The actual transformed entries are dominated by a geometric tail. -/
theorem tripleRoot_entry_majorant {p : ℕ} (hp : 2 ≤ p) (K i j m : ℕ) :
    |theta (theta (fun x => (tripleRootPoly ((p : ℝ)⁻¹) i).eval x *
        (tripleRootPoly ((p : ℝ)⁻¹) j).eval x / DK p K x)) (((p : ℝ)⁻¹) ^ (m + 1))| ≤
      ((16 / 3) * ((i : ℝ) + j + 1) ^ 2 * ((p : ℝ)⁻¹) ^ (aj i + aj j)) *
        (if max ((i + 2) / 3) ((j + 2) / 3) ≤ m + 1 then
          ((p : ℝ)⁻¹) ^ (m + 1 - max ((i + 2) / 3) ((j + 2) / 3)) else 0) := by
  have he : (fun x => (tripleRootPoly ((p : ℝ)⁻¹) i).eval x *
        (tripleRootPoly ((p : ℝ)⁻¹) j).eval x / DK p K x) =
      fun x => (tripleRootPoly ((p : ℝ)⁻¹) i).eval x *
        (tripleRootPoly ((p : ℝ)⁻¹) j).eval x * rationalWeight ((p : ℝ)⁻¹) K x := by
    rw [weight_eq_DK_inv]
    rfl
  rw [he]
  split_ifs with hR
  · exact tripleRoot_entry_surviving (inv_base_pos hp) (inv_base_le_half hp) K i j (m + 1)
      (by omega) hR
  · rw [tripleRoot_entry_vanish (inv_base_pos hp) (inv_base_le_half hp) K i j (m + 1)
      (by omega) (by omega)]
    simp

/-- The all-size transformed Gram entry bound from §2. -/
theorem tripleRoot_entry_sum_bound {p : ℕ} (hp : 2 ≤ p) (K i j : ℕ) :
    |Lfun p (fun x => (tripleRootPoly ((p : ℝ)⁻¹) i).eval x *
        (tripleRootPoly ((p : ℝ)⁻¹) j).eval x / DK p K x)| ≤
      12 * ((i : ℝ) + j + 1) ^ 2 * ((p : ℝ)⁻¹) ^ (aj i + aj j) := by
  have h := abs_tsum_le_geometricTail (inv_base_pos hp) (inv_base_le_half hp)
    (max ((i + 2) / 3) ((j + 2) / 3)) (summable_tripleRootGram_entry hp K i j)
    (show 0 ≤ (16 / 3) * ((i : ℝ) + j + 1) ^ 2 *
      ((p : ℝ)⁻¹) ^ (aj i + aj j) by positivity)
    (fun m => tripleRoot_entry_majorant hp K i j m)
  change |Lfun p _| ≤ _ at h
  have hpos : 0 ≤ ((i : ℝ) + j + 1) ^ 2 * ((p : ℝ)⁻¹) ^ (aj i + aj j) := by positivity
  nlinarith only [h, hpos]

/-- Proposition 2.1 for the actual Gram matrix, now including the full
analytic entry estimate and the determinant-preserving basis change. -/
theorem gram_det_le_proved {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    |(gramR p K).det| ≤
      (K.factorial : ℝ) * (12 * (2 * (K : ℝ) - 1) ^ 2) ^ K * ((p : ℝ)⁻¹) ^ bK K := by
  rw [← det_tripleRootGram hp K]
  apply tripleRoot_det_bound p K hp
  intro i j
  exact tripleRoot_entry_sum_bound hp K i.val j.val

end QZeta3
