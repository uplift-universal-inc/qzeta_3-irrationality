import QZeta3.CyclotomicBounds

/-!
# Elementary cyclotomic growth bounds

The uniform logarithmic bound and exponent sum are proved here. The finite
2-and-3 sieve in `QZeta3.DenominatorSieve` gives the sufficient cubic cost
`107/192 < 11/18` used by the irrationality proof. The manuscript's sharper
`321/(64π²)` asymptotic is not asserted by this formal development.

Local denominator clearing is proved using moving root-of-unity cluster
bases, integer row/column weights, the refined upper-node cancellation, and
the exact rank bound for the singular polynomial moment. Its public theorem
is `QZeta3.denominators_clear` in `QZeta3.Frozen.Prop41`.
-/

open Polynomial Finset Real

namespace QZeta3

variable {p : ℕ}

/-- `log Φ_d(p) ≤ φ(d) log p + 2` for `p ≥ 2`, `d ≥ 1`. -/
theorem log_cyclotomic_le (hp : 2 ≤ p) (d : ℕ) (hd : 1 ≤ d) :
    Real.log (Phi p d : ℝ) ≤ (Nat.totient d : ℝ) * Real.log p + 2 := by
  have h := cyclotomic_error_bound hp d hd
  have habs := le_abs_self (Real.log (Phi p d : ℝ) - (Nat.totient d : ℝ) * Real.log p)
  linarith

/-- `c_{K,d} ≤ K²/(4d) + 8K` for `K, d ≥ 1` (both ranges of eq. (4.1)). -/
theorem cApp_le (K d : ℕ) (hK : 1 ≤ K) (hd : 1 ≤ d) :
    (cApp K d : ℝ) ≤ (K : ℝ) ^ 2 / (4 * d) + 8 * K := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : (0 : ℝ) ≤ (K : ℝ) ^ 2 / (4 * d) := by positivity
  unfold cApp
  split_ifs with h
  · have hdK : (d : ℝ) ≤ K := by
      have : d ≤ K := by omega
      exact_mod_cast this
    have hx : (0 : ℚ) ≤ (K : ℚ) ^ 2 / (4 * d) + 2 * K + 17 * d / 16 := by positivity
    have h1 := Nat.ceil_lt_add_one hx
    have h2 : ((⌈(K : ℚ) ^ 2 / (4 * d) + 2 * K + 17 * d / 16⌉₊ : ℕ) : ℝ) <
        (((K : ℚ) ^ 2 / (4 * d) + 2 * K + 17 * d / 16 : ℚ) : ℝ) + 1 := by exact_mod_cast h1
    push_cast at h2
    linarith
  · have h1 : 5 * (K - d) + 3 ≤ 5 * K + 3 := by omega
    have h2 : ((5 * (K - d) + 3 : ℕ) : ℝ) ≤ ((5 * K + 3 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2 ⊢
    linarith

/-- `∑_{d=1}^{K} 1/d ≤ 1 + log K` (from `1 − x⁻¹ ≤ log x`, telescoping). -/
theorem sum_inv_le_one_add_log (K : ℕ) (hK : 1 ≤ K) :
    ∑ d ∈ Icc 1 K, (1 : ℝ) / d ≤ 1 + Real.log K := by
  induction K with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Finset.sum_Icc_succ_top (by omega)]
      have h1 := ih hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have h2 : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log n := by
        rw [← Real.log_div (by positivity) hnpos.ne']
        have h3 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) / n by positivity)
        have h4 : (1 : ℝ) - (((n + 1 : ℕ) : ℝ) / n)⁻¹ = 1 / ((n + 1 : ℕ) : ℝ) := by
          push_cast
          field_simp
          ring
        linarith
      linarith

/-- `∑_{d ≤ K} c_{K,d} ≤ (1/4 + (33/4)/log 2) K² log K` for `K ≥ 2`. -/
theorem sum_cApp_le :
    ∃ c : ℝ, ∀ K : ℕ, 2 ≤ K →
      (∑ d ∈ Icc 1 K, (cApp K d : ℝ)) ≤ c * (K : ℝ) ^ 2 * Real.log K := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨1 / 4 + (33 / 4) / Real.log 2, fun K hK => ?_⟩
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hlogK : Real.log 2 ≤ Real.log K :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hK)
  have hsum : ∑ d ∈ Icc 1 K, (1 : ℝ) / d ≤ 1 + Real.log K := sum_inv_le_one_add_log K (by omega)
  have hcard : ((Icc 1 K).card : ℝ) = K := by
    rw [Nat.card_Icc]; push_cast; ring
  calc ∑ d ∈ Icc 1 K, (cApp K d : ℝ)
      ≤ ∑ d ∈ Icc 1 K, ((K : ℝ) ^ 2 / 4 * (1 / d) + 8 * K) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have := cApp_le K d (by omega) (Finset.mem_Icc.mp hd).1
        have hrw : (K : ℝ) ^ 2 / (4 * d) = (K : ℝ) ^ 2 / 4 * (1 / d) := by ring
        linarith
    _ = (K : ℝ) ^ 2 / 4 * ∑ d ∈ Icc 1 K, (1 : ℝ) / d + 8 * K * K := by
        rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, nsmul_eq_mul, hcard]
        ring
    _ ≤ (K : ℝ) ^ 2 / 4 * (1 + Real.log K) + 8 * K * K := by
        have : (0 : ℝ) ≤ (K : ℝ) ^ 2 / 4 := by positivity
        nlinarith
    _ ≤ (1 / 4 + (33 / 4) / Real.log 2) * (K : ℝ) ^ 2 * Real.log K := by
        have hdiv : 1 ≤ Real.log K / Real.log 2 := by
          rw [le_div_iff₀ hlog2]; linarith
        have h : (K : ℝ) ^ 2 ≤ (K : ℝ) ^ 2 * (Real.log K / Real.log 2) := by
          have hK2 : (0 : ℝ) ≤ (K : ℝ) ^ 2 := by positivity
          nlinarith
        have hid : (1 / 4 + (33 / 4) / Real.log 2) * (K : ℝ) ^ 2 * Real.log K =
            1 / 4 * (K : ℝ) ^ 2 * Real.log K + 33 / 4 * ((K : ℝ) ^ 2 * (Real.log K / Real.log 2)) := by
          ring
        rw [hid]
        nlinarith [h]

theorem log_CK_eq (hp : 2 ≤ p) (K : ℕ) :
    Real.log (CK p K : ℝ) = ∑ d ∈ Icc 1 K, (cApp K d : ℝ) * Real.log (Phi p d : ℝ) := by
  unfold CK
  push_cast
  have hpos : ∀ d ∈ Icc 1 K, ((Phi p d : ℤ) : ℝ) ^ cApp K d ≠ 0 := by
    intro d _
    apply pow_ne_zero
    exact_mod_cast (Phi_pos hp d).ne'
  rw [Real.log_prod hpos]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Real.log_pow]

end QZeta3
