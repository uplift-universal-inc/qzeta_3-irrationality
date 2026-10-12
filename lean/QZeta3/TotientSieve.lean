import QZeta3.Elementary

/-! A finite two-prime upper bound for Euler's totient. -/
open Polynomial Finset Real
namespace QZeta3

noncomputable def sieveWeight (n : ℕ) : ℝ :=
  (if 2 ∣ n then 1/2 else 1) * (if 3 ∣ n then 2/3 else 1)

theorem totient_le_sieveWeight (n : ℕ) : (Nat.totient n : ℝ) ≤ n * sieveWeight n := by
  by_cases hn : n = 0
  · simp [hn]
  have hf : ∀ q ∈ n.primeFactors, (0 : ℚ) ≤ 1 - (q : ℚ)⁻¹ := by
    intro q hq
    have hq1 : (1 : ℚ) ≤ q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_le
    have hq0 : (0 : ℚ) < q := by linarith
    have := (inv_le_one₀ hq0).mpr hq1
    linarith
  have hs : ({2,3} : Finset ℕ).filter (fun q => q ∣ n) ⊆ n.primeFactors := by
    intro q hq
    obtain ⟨hq, hqn⟩ := Finset.mem_filter.mp hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hqn, hn⟩
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_three, hqn, hn⟩
  have hprod := Finset.prod_le_prod_of_subset_of_le_one₀ hs hf
    (fun q _ _ => sub_le_self (1 : ℚ) (by positivity : 0 ≤ (q : ℚ)⁻¹))
  have hbound : (Nat.totient n : ℚ) ≤ n *
      ((if 2 ∣ n then 1/2 else 1) * (if 3 ∣ n then 2/3 else 1) : ℚ) := by
    rw [Nat.totient_eq_mul_prod_factors]
    refine (mul_le_mul_of_nonneg_left hprod (by positivity)).trans_eq ?_
    congr 1
    rw [Finset.prod_filter]
    by_cases h2 : 2 ∣ n <;> by_cases h3 : 3 ∣ n <;> norm_num [h2, h3]
  have hr := (Rat.cast_le (K := ℝ)).mpr hbound
  push_cast at hr
  unfold sieveWeight
  split_ifs at hr ⊢ <;> norm_num at hr ⊢ <;> exact hr

theorem sieveWeight_nonneg (n : ℕ) : 0 ≤ sieveWeight n := by
  unfold sieveWeight
  split_ifs <;> norm_num

theorem sieveWeight_le_one (n : ℕ) : sieveWeight n ≤ 1 := by
  unfold sieveWeight
  split_ifs <;> norm_num

theorem sieveWeight_add_six (n : ℕ) : sieveWeight (n+6) = sieveWeight n := by
  simp [sieveWeight]

theorem sieveWeight_block_sum (n : ℕ) :
    ∑ i ∈ range 6, sieveWeight (6*n+i) = 4 := by
  norm_num [sieveWeight, Finset.sum_range_succ, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod]

theorem sieveWeight_six_mul_add (n i : ℕ) : sieveWeight (6*n+i) = sieveWeight i := by
  simp [sieveWeight, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod]

theorem sieveWeight_sum_blocks (n : ℕ) :
    ∑ i ∈ range (6*n), sieveWeight i = 4*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [sieveWeight_six_mul_add]
    norm_num [sieveWeight, Finset.sum_range_succ]
    ring

theorem sieveWeight_firstMoment_blocks (n : ℕ) :
    ∑ i ∈ range (6*n), sieveWeight i * (i : ℝ) = 12*(n : ℝ)^2 - n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [sieveWeight_six_mul_add]
    norm_num [sieveWeight, Finset.sum_range_succ]
    ring

theorem sieveWeight_secondMoment_blocks (n : ℕ) :
    ∑ i ∈ range (6*n), sieveWeight i * (i : ℝ)^2 = 48*(n : ℝ)^3 - 6*(n : ℝ)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [sieveWeight_six_mul_add]
    norm_num [sieveWeight, Finset.sum_range_succ]
    ring

theorem sieveWeight_moment_sandwich (n j : ℕ) :
    (∑ i ∈ range (6*(n/6)), sieveWeight i * (i : ℝ)^j) ≤
      ∑ i ∈ range n, sieveWeight i * (i : ℝ)^j ∧
    (∑ i ∈ range n, sieveWeight i * (i : ℝ)^j) ≤
      ∑ i ∈ range (6*(n/6+1)), sieveWeight i * (i : ℝ)^j := by
  constructor <;> apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply Finset.range_mono
    omega
  · intro i _ _; exact mul_nonneg (sieveWeight_nonneg i) (by positivity)
  · apply Finset.range_mono
    omega
  · intro i _ _; exact mul_nonneg (sieveWeight_nonneg i) (by positivity)

theorem sieveWeight_sum_bounds (n : ℕ) :
    2/3*(n : ℝ)-4 ≤ ∑ i ∈ range n, sieveWeight i ∧
    (∑ i ∈ range n, sieveWeight i) ≤ 2/3*(n : ℝ)+4 := by
  have hs := sieveWeight_moment_sandwich n 0
  simp only [pow_zero, mul_one, sieveWeight_sum_blocks] at hs
  have hn : (6 : ℝ)*(n/6 : ℕ) ≤ n := by exact_mod_cast Nat.mul_div_le n 6
  have hn' : (n : ℝ) ≤ 6*((n/6 : ℕ)+1) := by exact_mod_cast (show n ≤ 6*(n/6+1) by omega)
  push_cast at hs hn hn'
  constructor <;> linarith [hs.1, hs.2]

theorem sieveWeight_firstMoment_bounds (n : ℕ) :
    (n : ℝ)^2/3 - 20*((n : ℝ)+1) ≤ ∑ i ∈ range n, sieveWeight i * i ∧
    (∑ i ∈ range n, sieveWeight i * i) ≤ (n : ℝ)^2/3 + 20*((n : ℝ)+1) := by
  have hs := sieveWeight_moment_sandwich n 1
  simp only [pow_one, sieveWeight_firstMoment_blocks] at hs
  have hr : n % 6 < 6 := Nat.mod_lt n (by norm_num)
  have hn : (n : ℝ) = 6*(n/6 : ℕ)+(n%6 : ℕ) := by exact_mod_cast (show n=6*(n/6)+n%6 by omega)
  have hq : (0 : ℝ) ≤ (n/6 : ℕ) := by positivity
  push_cast at hs
  rw [hn]
  interval_cases h : n%6 <;> norm_num [h] <;> constructor <;> nlinarith [hs.1, hs.2]

theorem sieveWeight_secondMoment_bounds (n : ℕ) :
    2/9*(n : ℝ)^3 - 100*((n : ℝ)+1)^2 ≤ ∑ i ∈ range n, sieveWeight i * (i : ℝ)^2 ∧
    (∑ i ∈ range n, sieveWeight i * (i : ℝ)^2) ≤ 2/9*(n : ℝ)^3 + 100*((n : ℝ)+1)^2 := by
  have hs := sieveWeight_moment_sandwich n 2
  simp only [sieveWeight_secondMoment_blocks] at hs
  have hr : n % 6 < 6 := Nat.mod_lt n (by norm_num)
  have hn : (n : ℝ) = 6*(n/6 : ℕ)+(n%6 : ℕ) := by exact_mod_cast (show n=6*(n/6)+n%6 by omega)
  have hq : (0 : ℝ) ≤ (n/6 : ℕ) := by positivity
  push_cast at hs
  rw [hn]
  interval_cases h : n%6 <;> norm_num [h] <;> constructor <;> nlinarith [hs.1, hs.2]
end QZeta3
