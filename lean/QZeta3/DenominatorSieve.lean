import QZeta3.Denominators
import QZeta3.TotientSieve

open Finset Real
namespace QZeta3

noncomputable def lowCost (K d : ℕ) : ℝ := (K : ℝ)^2/4 + (2*K+1)*d + 17*(d : ℝ)^2/16
noncomputable def highCost (K d : ℕ) : ℝ := (5*(K : ℝ)+3)*d - 5*(d : ℝ)^2

theorem cApp_totient_low (K d : ℕ) (hd : 2*d ≤ K) :
    (cApp K d : ℝ)*(Nat.totient d : ℝ) ≤ lowCost K d * sieveWeight d := by
  by_cases hd0 : d=0
  · simp only [hd0, Nat.totient_zero, Nat.cast_zero, mul_zero]
    exact mul_nonneg (by simp [lowCost]; positivity) (sieveWeight_nonneg 0)
  have hdpos : (0 : ℝ)<d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hc : (cApp K d : ℝ) ≤ (K : ℝ)^2/(4*d)+2*K+17*d/16+1 := by
    unfold cApp
    simp only [hd, ite_true]
    have h := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ (K : ℚ)^2/(4*d)+2*K+17*d/16 by positivity)
    have hr := (Rat.cast_lt (K := ℝ)).mpr h
    push_cast at hr
    exact hr.le
  have hphi := totient_le_sieveWeight d
  calc (cApp K d : ℝ)*(Nat.totient d : ℝ)
      ≤ ((K : ℝ)^2/(4*d)+2*K+17*d/16+1)*(d*sieveWeight d) :=
        mul_le_mul hc hphi (by positivity) (by positivity)
    _ = lowCost K d * sieveWeight d := by unfold lowCost; field_simp; ring

theorem cApp_totient_high (K d : ℕ) (hd : K < 2*d) (hdK : d ≤ K) :
    (cApp K d : ℝ)*(Nat.totient d : ℝ) ≤ highCost K d * sieveWeight d := by
  have hc : (cApp K d : ℝ) = 5*((K : ℝ)-d)+3 := by
    simp [cApp, show ¬2*d≤K by omega, Nat.cast_sub hdK]
  rw [hc]
  have h0 : (0 : ℝ) ≤ 5*((K : ℝ)-d)+3 := by
    have : (d : ℝ) ≤ K := by exact_mod_cast hdK
    linarith
  calc _ ≤ (5*((K : ℝ)-d)+3)*(d*sieveWeight d) :=
      mul_le_mul_of_nonneg_left (totient_le_sieveWeight d) h0
    _ = highCost K d*sieveWeight d := by unfold highCost; ring

theorem sieve_low_sum (K M : ℕ) :
    (∑ d ∈ range M, lowCost K d*sieveWeight d) =
      (K : ℝ)^2/4 * (∑ d ∈ range M, sieveWeight d) +
      (2*K+1)*(∑ d ∈ range M, sieveWeight d*d) +
      17/16*(∑ d ∈ range M, sieveWeight d*(d : ℝ)^2) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  unfold lowCost
  ring

theorem sieve_high_sum (K M : ℕ) :
    (∑ d ∈ range M, highCost K d*sieveWeight d) =
      (5*(K : ℝ)+3)*(∑ d ∈ range M, sieveWeight d*d) -
      5*(∑ d ∈ range M, sieveWeight d*(d : ℝ)^2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  unfold highCost
  ring

theorem sum_cApp_totient_sieve (K : ℕ) :
    (∑ d ∈ Icc 1 K, (cApp K d : ℝ)*(Nat.totient d : ℝ)) ≤
    (∑ d ∈ range (K/2+1), lowCost K d*sieveWeight d) +
    (∑ d ∈ range (K+1), highCost K d*sieveWeight d) -
    (∑ d ∈ range (K/2+1), highCost K d*sieveWeight d) := by
  have hI : Icc 1 K = Ico 1 (K+1) := by ext d; simp
  rw [hI, Finset.sum_Ico_eq_sub _ (by omega)]
  simp only [Finset.sum_range_one, Nat.totient_zero, Nat.cast_zero, mul_zero, sub_zero]
  have hsplit : K+1 = (K/2+1)+((K+1)-(K/2+1)) := by omega
  conv_lhs => rw [hsplit, Finset.sum_range_add]
  have hlo : (∑ d ∈ range (K/2+1), (cApp K d : ℝ)*(Nat.totient d : ℝ)) ≤
      ∑ d ∈ range (K/2+1), lowCost K d*sieveWeight d := by
    apply Finset.sum_le_sum
    intro d hd
    exact cApp_totient_low K d (by have := Finset.mem_range.mp hd; omega)
  have hhi : (∑ i ∈ range ((K+1)-(K/2+1)),
      (cApp K (K/2+1+i) : ℝ)*(Nat.totient (K/2+1+i) : ℝ)) ≤
      ∑ i ∈ range ((K+1)-(K/2+1)), highCost K (K/2+1+i)*sieveWeight (K/2+1+i) := by
    apply Finset.sum_le_sum
    intro d hd
    apply cApp_totient_high K (K/2+1+d)
    · omega
    · have := Finset.mem_range.mp hd; omega
  have hh := Finset.sum_range_add (fun d => highCost K d*sieveWeight d)
    (K/2+1) ((K+1)-(K/2+1))
  rw [← hsplit] at hh
  linarith

/-- A sufficient cubic totient cost, using only the primes 2 and 3. -/
theorem sum_cApp_totient_rational_le (K : ℕ) :
    (∑ d ∈ Icc 1 K, (cApp K d : ℝ)*(Nat.totient d : ℝ)) ≤
      107/192*(K : ℝ)^3 + 10000*((K : ℝ)+1)^2 := by
  have hs := sum_cApp_totient_sieve K
  rw [sieve_low_sum, sieve_high_sum, sieve_high_sum] at hs
  let M := K/2+1
  let N := K+1
  have hm0 := (sieveWeight_sum_bounds M).2
  have hm1 := (sieveWeight_firstMoment_bounds M).1
  have hm2 := (sieveWeight_secondMoment_bounds M).2
  have hn1 := (sieveWeight_firstMoment_bounds N).2
  have hn2 := (sieveWeight_secondMoment_bounds N).1
  have hm0' := mul_le_mul_of_nonneg_left hm0 (show (0 : ℝ) ≤ (K : ℝ)^2/4 by positivity)
  have hm1' := mul_le_mul_of_nonneg_left hm1 (show (0 : ℝ) ≤ 3*K+2 by positivity)
  have hm2' := mul_le_mul_of_nonneg_left hm2 (show (0 : ℝ) ≤ 97/16 by positivity)
  have hn1' := mul_le_mul_of_nonneg_left hn1 (show (0 : ℝ) ≤ 5*K+3 by positivity)
  have hn2' := mul_le_mul_of_nonneg_left hn2 (show (0 : ℝ) ≤ 5 by positivity)
  have hbound : (∑ d ∈ Icc 1 K, (cApp K d : ℝ)*(Nat.totient d : ℝ)) ≤
      (K : ℝ)^2/4 * (2/3*M+4) - (3*K+2)*((M : ℝ)^2/3-20*(M+1)) +
      97/16*(2/9*(M : ℝ)^3+100*(M+1)^2) +
      (5*K+3)*((N : ℝ)^2/3+20*(N+1)) - 5*(2/9*(N : ℝ)^3-100*(N+1)^2) := by
    dsimp [M, N] at *
    nlinarith only [hs, hm0', hm1', hm2', hn1', hn2']
  refine hbound.trans ?_
  dsimp [M, N]
  have hr : K % 2 < 2 := Nat.mod_lt K (by norm_num)
  have hK : (K : ℝ) = 2*(K/2 : ℕ)+(K%2 : ℕ) := by
    exact_mod_cast (show K=2*(K/2)+K%2 by omega)
  have hq : (0 : ℝ) ≤ (K/2 : ℕ) := by positivity
  push_cast
  rw [hK]
  interval_cases h : K%2 <;> norm_num [h] <;> nlinarith

theorem rational_cost_margin : (0 : ℝ) < 11/18-107/192 := by norm_num

theorem sum_cApp_totient_rational_asymptotic :
    ∃ c : ℝ, ∀ K : ℕ, 2 ≤ K →
      (∑ d ∈ Icc 1 K, (cApp K d : ℝ)*(Nat.totient d : ℝ)) ≤
        107/192*(K : ℝ)^3+c*(K : ℝ)^2*Real.log K := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨40000/Real.log 2, fun K hK => ?_⟩
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1≤K by omega)
  have hlK : Real.log 2 ≤ Real.log K := Real.log_le_log (by norm_num) (by exact_mod_cast hK)
  have hdiv : 1 ≤ Real.log K/Real.log 2 := by rw [le_div_iff₀ hl2]; simpa using hlK
  have hmul := mul_le_mul_of_nonneg_left hdiv (show (0 : ℝ) ≤ 40000*(K : ℝ)^2 by positivity)
  have hs := sum_cApp_totient_rational_le K
  have heq : 40000/Real.log 2*(K : ℝ)^2*Real.log K =
      40000*(K : ℝ)^2*(Real.log K/Real.log 2) := by ring
  rw [heq]
  nlinarith [sq_nonneg ((K : ℝ)-1)]

/-- Cyclotomic growth sufficient for the irrationality criterion, with a rational cubic cost. -/
theorem log_CK_rational_le {p : ℕ} (hp : 2 ≤ p) :
    ∃ c : ℝ, ∀ K : ℕ, 2 ≤ K →
      Real.log (CK p K : ℝ) ≤
        107/192*(K : ℝ)^3*Real.log p+c*(K : ℝ)^2*Real.log K := by
  obtain ⟨c₁, h₁⟩ := sum_cApp_totient_rational_asymptotic
  obtain ⟨c₂, h₂⟩ := sum_cApp_le
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  refine ⟨c₁ * Real.log p + 2 * c₂, fun K hK => ?_⟩
  rw [log_CK_eq hp K]
  calc ∑ d ∈ Icc 1 K, (cApp K d : ℝ) * Real.log (Phi p d : ℝ)
      ≤ ∑ d ∈ Icc 1 K, (cApp K d : ℝ) * ((Nat.totient d : ℝ) * Real.log p + 2) := by
        refine Finset.sum_le_sum fun d hd => ?_
        exact mul_le_mul_of_nonneg_left (log_cyclotomic_le hp d (Finset.mem_Icc.mp hd).1)
          (by positivity)
    _ = Real.log p * (∑ d ∈ Icc 1 K, (cApp K d : ℝ) * (Nat.totient d : ℝ)) +
          2 * (∑ d ∈ Icc 1 K, (cApp K d : ℝ)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d _ => ?_
        ring
    _ ≤ Real.log p * (107/192*(K : ℝ)^3+c₁*(K : ℝ)^2*Real.log K) +
          2 * (c₂ * (K : ℝ) ^ 2 * Real.log K) := by
        exact add_le_add (mul_le_mul_of_nonneg_left (h₁ K hK) hlogp.le)
          (mul_le_mul_of_nonneg_left (h₂ K hK) (by norm_num))
    _ = 107/192*(K : ℝ)^3*Real.log p+
          (c₁*Real.log p+2*c₂)*(K : ℝ)^2*Real.log K := by ring
end QZeta3
