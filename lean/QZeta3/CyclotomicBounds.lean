import QZeta3.Elementary

/-! Uniform cyclotomic logarithm error, proved by Möbius inversion and a finite geometric bound. -/
open Polynomial Finset Real
open scoped ArithmeticFunction.Moebius
namespace QZeta3
variable {p : ℕ}

theorem sum_log_Phi (hp : 2 ≤ p) (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, Real.log (Phi p d : ℝ) = Real.log ((p : ℝ)^n - 1) := by
  have he (d : ℕ) : (Phi p d : ℝ) = (cyclotomic d ℝ).eval (p : ℝ) := by
    simpa [Phi] using (cyclotomic.eval_apply (p : ℤ) d (Int.castRingHom ℝ)).symm
  simp_rw [he]
  rw [← Real.log_prod (fun d _ => (cyclotomic_pos' d (by exact_mod_cast (show 1 < p by omega))).ne'),
    ← eval_prod, prod_cyclotomic_eq_X_pow_sub_one hn]
  simp

theorem sum_cyclotomic_error (hp : 2 ≤ p) (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, (Real.log (Phi p d : ℝ) - (Nat.totient d : ℝ) * Real.log p) =
      Real.log (1 - ((p : ℝ)⁻¹)^n) := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_log_Phi hp n hn]
  have hs : (∑ d ∈ n.divisors, (Nat.totient d : ℝ)) = n := by
    exact_mod_cast Nat.sum_totient n
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hpow : (1 : ℝ) < (p : ℝ)^n := one_lt_pow₀ hp1 hn.ne'
  rw [hs, ← Real.log_pow, ← Real.log_div (by linarith) (by positivity)]
  congr 1
  rw [inv_pow]
  field_simp

theorem error_log_bound (hp : 2 ≤ p) (a : ℕ) (ha : 0 < a) :
    |Real.log (1 - ((p : ℝ)⁻¹)^a)| ≤ 2 * ((1 / 2 : ℝ)^a) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hppos : (0 : ℝ) < p := by linarith
  have hpi : (p : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ hppos).2
    linarith
  have ht0 : 0 ≤ ((p : ℝ)⁻¹)^a := by positivity
  have ht : ((p : ℝ)⁻¹)^a ≤ ((1 / 2 : ℝ)^a) :=
    pow_le_pow_left₀ (by positivity) hpi a
  have ht2 : ((1 / 2 : ℝ)^a) ≤ 1 / 2 := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) ha
  have hlog : Real.log (1 - ((p : ℝ)⁻¹)^a) ≤ 0 :=
    Real.log_nonpos (by linarith) (by linarith)
  rw [abs_of_nonpos hlog]
  have hlow := Real.one_sub_inv_le_log_of_pos (show 0 < 1 - ((p : ℝ)⁻¹)^a by linarith)
  have hi : (1 - ((p : ℝ)⁻¹)^a)⁻¹ ≤ 1 + 2 * ((p : ℝ)⁻¹)^a := by
    apply (inv_le_iff_one_le_mul₀ (by linarith : 0 < 1 - ((p : ℝ)⁻¹)^a)).2
    nlinarith
  linarith

theorem sum_half_pow_le (n : ℕ) : ∑ d ∈ Icc 1 n, ((1/2 : ℝ)^d) ≤ 1 := by
  suffices h : ∑ d ∈ Icc 1 n, ((1/2 : ℝ)^d) = 1 - (1/2 : ℝ)^n by
    rw [h]
    exact sub_le_self _ (by positivity)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, pow_succ]
    ring

theorem cyclotomic_error_bound (hp : 2 ≤ p) (d : ℕ) (hd : 0 < d) :
    |Real.log (Phi p d : ℝ) - (Nat.totient d : ℝ) * Real.log p| ≤ 2 := by
  have hm := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp (sum_cyclotomic_error hp)) d hd
  rw [← hm, Nat.sum_divisorsAntidiagonal' (fun a b => (ArithmeticFunction.moebius a : ℝ) * Real.log (1 - ((p : ℝ)⁻¹)^b))]
  calc |∑ a ∈ d.divisors, (ArithmeticFunction.moebius (d/a) : ℝ) * Real.log (1 - ((p : ℝ)⁻¹)^a)|
      ≤ ∑ a ∈ d.divisors, |(ArithmeticFunction.moebius (d/a) : ℝ) * Real.log (1 - ((p : ℝ)⁻¹)^a)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ d.divisors, 2 * (1/2 : ℝ)^a := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul]
      have hmu : |(ArithmeticFunction.moebius (d/a) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d/a))
      calc _ ≤ 1 * |Real.log (1 - ((p : ℝ)⁻¹)^a)| :=
          mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
        _ ≤ _ := by simpa using error_log_bound hp a (Nat.pos_of_mem_divisors ha)
    _ ≤ ∑ a ∈ Icc 1 d, 2 * (1/2 : ℝ)^a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,
          Nat.le_of_dvd hd (Nat.dvd_of_mem_divisors ha)⟩
      · intro a _ _; positivity
    _ ≤ 2 := by rw [← Finset.mul_sum]; linarith [sum_half_pow_le d]
end QZeta3
