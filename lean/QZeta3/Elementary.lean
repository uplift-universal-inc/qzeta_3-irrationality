import QZeta3.Defs

/-!
# Elementary facts (all proved)

* Summability and positivity of the series defining `ξ_p` (statement-fidelity audit of `xi`).
* The reciprocity `g(1/y) = −g(y)` of §3 and the identification `S_a = ∑_{b ≤ a} g(p^{−b})`.
* Exact values of `A_K`, `e_K` over `ℝ`, and the lower bound `9 b_K ≥ K³ − K` used in the assembly.
* `deg Δ_K ≤ K` (the exact degree is part of Proposition 3.1).
* Positivity of the cyclotomic multiplier `C_K` and of the margin `11/18 − 321/(64π²)`.
-/

open Polynomial Finset Filter Topology

namespace QZeta3

variable {p : ℕ}

/-! ### Summability of ξ_p -/

theorem one_lt_pow_succ (hp : 2 ≤ p) (n : ℕ) : (1 : ℝ) < (p : ℝ) ^ (n + 1) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  exact one_lt_pow₀ (by linarith) (Nat.succ_ne_zero n)

theorem two_le_pow_succ (hp : 2 ≤ p) (n : ℕ) : (2 : ℝ) ≤ (p : ℝ) ^ (n + 1) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    _ ≤ (p : ℝ) ^ (n + 1) := pow_le_pow_left₀ (by norm_num) h2 _

theorem term_nonneg (hp : 2 ≤ p) (n : ℕ) : 0 ≤ term p (n + 1) := by
  unfold term
  have := one_lt_pow_succ hp n
  exact div_nonneg (sq_nonneg _) (by linarith)

theorem term_pos (hp : 2 ≤ p) (n : ℕ) : 0 < term p (n + 1) := by
  unfold term
  have := one_lt_pow_succ hp n
  exact div_pos (by positivity) (by linarith)

/-- The comparison `n²/(pⁿ − 1) ≤ 2 n² p^{−n}` (for `n ≥ 1`), since `pⁿ − 1 ≥ pⁿ/2`. -/
theorem term_le (hp : 2 ≤ p) (n : ℕ) :
    term p (n + 1) ≤ 2 * ((((n + 1 : ℕ) : ℝ)) ^ 2 * ((p : ℝ)⁻¹) ^ (n + 1)) := by
  unfold term
  have hP := two_le_pow_succ hp n
  have hPpos : 0 < (p : ℝ) ^ (n + 1) := by linarith
  calc (((n + 1 : ℕ) : ℝ)) ^ 2 / ((p : ℝ) ^ (n + 1) - 1)
      ≤ (((n + 1 : ℕ) : ℝ)) ^ 2 / ((p : ℝ) ^ (n + 1) / 2) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)
    _ = 2 * ((((n + 1 : ℕ) : ℝ)) ^ 2 * ((p : ℝ)⁻¹) ^ (n + 1)) := by
        rw [inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
        ring

theorem summable_term (hp : 2 ≤ p) : Summable (fun n : ℕ => term p (n + 1)) := by
  have hr : ‖(p : ℝ)⁻¹‖ < 1 := by
    rw [norm_inv, Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (show 1 < p by omega))
  have h1 : Summable (fun n : ℕ => (n : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have h2 : Summable (fun n : ℕ => 2 * ((((n + 1 : ℕ) : ℝ)) ^ 2 * ((p : ℝ)⁻¹) ^ (n + 1))) :=
    ((summable_nat_add_iff 1).mpr h1).mul_left 2
  exact Summable.of_nonneg_of_le (term_nonneg hp) (term_le hp) h2

/-- `ξ_p` is the sum of its (convergent) series: no `tsum` junk value is involved. -/
theorem hasSum_xi (hp : 2 ≤ p) : HasSum (fun n : ℕ => term p (n + 1)) (xi p) :=
  (summable_term hp).hasSum

theorem xi_pos (hp : 2 ≤ p) : 0 < xi p :=
  (summable_term hp).tsum_pos (fun n => term_nonneg hp n) 0 (term_pos hp 0)

/-! ### The function `g` of §3 and the partial sums `S_a` -/

/-- `g(y) = y(1+y)/(1−y)³ = ∑_{n ≥ 1} n² yⁿ` (as a rational function). -/
def g (y : ℚ) : ℚ := y * (1 + y) / (1 - y) ^ 3

/-- The reciprocity `g(y⁻¹) = −g(y)` (§3, used for `S_a = −Z + H(p^a)`). -/
theorem g_inv {y : ℚ} (hy0 : y ≠ 0) (hy1 : y ≠ 1) : g y⁻¹ = -g y := by
  unfold g
  have h1 : (1 : ℚ) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy1)
  have h2 : (1 : ℚ) - y⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; intro h; apply hy1; rw [← inv_inv y, ← h, inv_one]
  field_simp
  ring

/-- `S_a = ∑_{b=1}^{a} g(p^{−b})` (the definition (1.5) in the form used in §1). -/
theorem S_eq_sum_g (hp : 2 ≤ p) (a : ℕ) : S p a = ∑ b ∈ Icc 1 a, g ((p : ℚ) ^ b)⁻¹ := by
  unfold S g
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
  have hp1 : (1 : ℚ) < (p : ℚ) ^ b :=
    one_lt_pow₀ (by exact_mod_cast (show 1 < p by omega)) (by omega)
  have hne : (p : ℚ) ^ b - 1 ≠ 0 := by linarith
  have hne' : (1 : ℚ) - ((p : ℚ) ^ b)⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : ((p : ℚ) ^ b)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    rw [← h] at this; exact lt_irrefl _ this
  have hpos : (p : ℚ) ^ b ≠ 0 := by positivity
  field_simp

/-! ### Exact values of `A_K`, `e_K`; the lower bound for `b_K` -/

theorem AK_cast (K : ℕ) : (AK K : ℝ) = K * (K + 1) / 2 := by
  unfold AK
  have h2 : 2 ∣ K * (K + 1) := (Nat.even_mul_succ_self K).two_dvd
  rw [Nat.cast_div h2 (by norm_num)]
  push_cast
  ring

theorem eK_cast {K : ℕ} (hK : 1 ≤ K) : (eK K : ℝ) = K * ((K : ℝ) ^ 2 - 1) / 2 := by
  unfold eK
  rw [Nat.cast_mul, AK_cast, Nat.cast_sub hK]
  push_cast
  ring

/-- `t ≤ 3⌈t/3⌉`. -/
theorem le_three_mul_ceil_div_three (t : ℕ) : t ≤ 3 * ((t + 2) / 3) := by omega

theorem sum_Icc_id_mul_two (j : ℕ) : (∑ t ∈ Icc 1 j, t) * 2 = j * (j + 1) := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_mul, ih]
    ring

/-- `j(j+1) ≤ 6 a_j`, from `a_j = ∑_{t ≤ j} ⌈t/3⌉ ≥ ∑_{t ≤ j} t/3`. -/
theorem mul_succ_le_six_aj (j : ℕ) : j * (j + 1) ≤ 6 * aj j := by
  unfold aj
  have h : ∑ t ∈ Icc 1 j, t ≤ ∑ t ∈ Icc 1 j, 3 * ((t + 2) / 3) :=
    Finset.sum_le_sum fun t _ => le_three_mul_ceil_div_three t
  rw [← Finset.mul_sum] at h
  rw [← sum_Icc_id_mul_two]
  omega

theorem sum_range_cubic (K : ℕ) :
    ∑ j ∈ range K, (3 * (j : ℝ) * ((j : ℝ) + 1)) = (K : ℝ) ^ 3 - K := by
  induction K with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- `K³ − K ≤ 9 b_K` (the manuscript's exact value is `b_K = (K³ + 3K² − c_{K mod 3})/9`). -/
theorem bK_ge (K : ℕ) : (K : ℝ) ^ 3 - K ≤ 9 * (bK K : ℝ) := by
  unfold bK
  rw [← sum_range_cubic]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := mul_succ_le_six_aj j
  have h' : (j : ℝ) * ((j : ℝ) + 1) ≤ 6 * (aj j : ℝ) := by exact_mod_cast h
  nlinarith

/-! ### Degree bound and positivity facts -/

/-- `deg Δ_K ≤ K`: every entry of the Hankel matrix is affine in `X`. -/
theorem natDegree_Delta_le (p K : ℕ) : (Delta p K).natDegree ≤ K := by
  unfold Delta
  simpa [Fintype.card_fin] using
    Polynomial.natDegree_det_X_add_C_le (hankelLin p K) (hankelConst p K)

/-- `C_K > 0`: every cyclotomic value `Φ_d(p)`, `p ≥ 2`, is positive. -/
theorem Phi_pos (hp : 2 ≤ p) (d : ℕ) : 0 < Phi p d :=
  cyclotomic_pos' d (by exact_mod_cast (show 1 < p by omega))

theorem CK_pos (hp : 2 ≤ p) (K : ℕ) : 0 < CK p K := by
  unfold CK
  exact Finset.prod_pos fun d _ => pow_pos (Phi_pos hp d) _

/-- The margin `11/18 − 321/(64π²)` is positive (`π > 3.14` suffices: `π² > 315/32`). -/
theorem margin_pos : 0 < margin := by
  unfold margin
  have hpi := Real.pi_gt_d2
  have hpi2 : (9.8 : ℝ) < Real.pi ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < 64 * Real.pi ^ 2 := by positivity
  rw [sub_pos, div_lt_div_iff₀ hpos (by norm_num)]
  nlinarith

end QZeta3
