import QZeta3.Main
import QZeta3.ElementaryContent

/-!
# The elementary second proof: assembly and rational growth margin

This variant uses the same moving-denominator Hankel determinants and the same
analytic, cyclotomic-denominator and nonvanishing theorems as the first proof.
Its alternative coefficient-content argument is combined with the elementary
finite-sieve growth cost `9/16`, leaving the exact positive margin `7/144`.

The already checked two-prime sieve gives the slightly stronger cost `107/192`;
weakening it to `9/16` gives precisely the sufficient bound of the second write-up.
No prime-number theorem or asymptotic formula for the summatory totient is used.
The final irrationality argument is assembled directly from the polynomial
approximation criterion, without invoking `irrational_xi` or `theorem11`.
-/

open Polynomial Finset Filter Topology

namespace QZeta3

variable {p : ℕ}

/-- Exact cubic margin in the elementary second proof. -/
theorem elementary_cost_margin_eq : (11 / 18 - 9 / 16 : ℝ) = 7 / 144 := by
  norm_num

/-- The elementary second proof has a strictly positive cubic margin. -/
theorem elementary_cost_margin : (0 : ℝ) < 11 / 18 - 9 / 16 := by
  norm_num

/-- The finite two-prime sieve implies the second proof's `9/16` cost. -/
theorem sum_cApp_totient_elementary_asymptotic :
    ∃ c : ℝ, ∀ K : ℕ, 2 ≤ K →
      (∑ d ∈ Icc 1 K, (cApp K d : ℝ) * (Nat.totient d : ℝ)) ≤
        9 / 16 * (K : ℝ) ^ 3 + c * (K : ℝ) ^ 2 * Real.log K := by
  obtain ⟨c, hc⟩ := sum_cApp_totient_rational_asymptotic
  refine ⟨c, fun K hK => (hc K hK).trans ?_⟩
  have hlead : (107 / 192 : ℝ) * (K : ℝ) ^ 3 ≤ 9 / 16 * (K : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  exact add_le_add hlead le_rfl

/-- Elementary cyclotomic growth bound, with no sharp totient asymptotic. -/
theorem log_CK_elementary_le (hp : 2 ≤ p) :
    ∃ c : ℝ, ∀ K : ℕ, 2 ≤ K →
      Real.log (CK p K : ℝ) ≤
        9 / 16 * (K : ℝ) ^ 3 * Real.log p + c * (K : ℝ) ^ 2 * Real.log K := by
  obtain ⟨c, hc⟩ := log_CK_rational_le hp
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  refine ⟨c, fun K hK => (hc K hK).trans ?_⟩
  have hlead : (107 / 192 : ℝ) * (K : ℝ) ^ 3 ≤ 9 / 16 * (K : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  exact add_le_add (mul_le_mul_of_nonneg_right hlead hlogp) le_rfl

/-- Logarithmic decay with the elementary second proof's explicit `7/144` margin. -/
theorem log_pow_mul_epsK_elementary_le (hp : 2 ≤ p) {c : ℝ}
    (hC : ∀ K : ℕ, 2 ≤ K → Real.log (CK p K) ≤
      9 / 16 * (K : ℝ) ^ 3 * Real.log p + c * (K : ℝ) ^ 2 * Real.log K)
    (b : ℕ) (hb : 0 < b) (K : ℕ) (hK : 2 ≤ K) :
    Real.log ((b : ℝ) ^ K * epsK p K) ≤
      -(7 / 144) * (K : ℝ) ^ 3 * Real.log p + c * (K : ℝ) ^ 2 * Real.log K +
        (Real.log b + Real.log 48 + Real.log p + 3) * (K : ℝ) ^ 2 := by
  simpa only [elementary_cost_margin_eq] using
    log_pow_mul_epsK_le_of_cost hp hC b hb K hK

/-- Unconditional decay for the elementary second proof. -/
theorem tendsto_pow_mul_epsK_elementary (hp : 2 ≤ p) (b : ℕ) (hb : 0 < b) :
    Tendsto (fun K : ℕ => (b : ℝ) ^ K * epsK p K) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := log_CK_elementary_le hp
  exact tendsto_pow_mul_epsK_of_cost hp (sub_pos.mp elementary_cost_margin) hc b hb

/-- Gluing any coefficient-content proof to the shared cyclotomic denominator theorem. -/
theorem PK_coeff_den_of_content (hp : 2 ≤ p)
    (hcontent : ∀ K i : ℕ,
      Nat.Coprime ((Delta p K).coeff i / (p : ℚ) ^ eK K).den p)
    (K i : ℕ) : ((PK p K).coeff i).den = 1 := by
  unfold PK
  rw [Polynomial.coeff_mul_C]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hrew : (Delta p K).coeff i * ((CK p K : ℚ) / (p : ℚ) ^ eK K) =
      (CK p K : ℚ) * ((Delta p K).coeff i / (p : ℚ) ^ eK K) := by ring
  rw [hrew]
  have hcop : Nat.Coprime
      ((CK p K : ℚ) * ((Delta p K).coeff i / (p : ℚ) ^ eK K)).den p := by
    have hdvd := Rat.mul_den_dvd (CK p K : ℚ) ((Delta p K).coeff i / (p : ℚ) ^ eK K)
    rw [Rat.den_intCast, one_mul] at hdvd
    exact Nat.Coprime.coprime_dvd_left hdvd (hcontent K i)
  obtain ⟨m, hm⟩ := denominators_clear hp K i
  have hm' :
      ((CK p K : ℚ) * ((Delta p K).coeff i / (p : ℚ) ^ eK K) *
        (p : ℚ) ^ (m + eK K)).den = 1 := by
    have : (CK p K : ℚ) * ((Delta p K).coeff i / (p : ℚ) ^ eK K) *
        (p : ℚ) ^ (m + eK K) =
        (CK p K : ℚ) * (Delta p K).coeff i * (p : ℚ) ^ m := by
      have hpe : (p : ℚ) ^ eK K ≠ 0 := pow_ne_zero _ hp0
      calc
        (CK p K : ℚ) * ((Delta p K).coeff i / (p : ℚ) ^ eK K) *
            (p : ℚ) ^ (m + eK K) =
            (CK p K : ℚ) * (Delta p K).coeff i * (p : ℚ) ^ m *
              ((p : ℚ) ^ eK K / (p : ℚ) ^ eK K) := by rw [pow_add]; ring
        _ = (CK p K : ℚ) * (Delta p K).coeff i * (p : ℚ) ^ m := by
          rw [div_self hpe, mul_one]
    rw [this]
    exact hm
  exact den_eq_one_of_coprime (show 0 < p by omega) hcop hm'

/-- Direct criterion assembly with elementary growth and a supplied content proof.
This does not use the first proof's irrationality theorem. -/
theorem irrational_xi_elementary_of_content (hp : 2 ≤ p)
    (hcontent : ∀ K i : ℕ,
      Nat.Coprime ((Delta p K).coeff i / (p : ℚ) ^ eK K).den p) :
    Irrational (xi p) := by
  refine irrational_of_poly_approx (xi p) (PK p) (natDegree_PK_le p)
    (PK_coeff_den_of_content hp hcontent) (epsK p) (abs_aeval_PK_le hp)
    (tendsto_pow_mul_epsK_elementary hp) ?_
  intro N
  obtain ⟨K, hKN, hne⟩ := frequently_ne_zero hp N
  refine ⟨K, hKN, ?_⟩
  rw [aeval_PK]
  have hCK : (CK p K : ℝ) ≠ 0 := by exact_mod_cast (CK_pos hp K).ne'
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  exact mul_ne_zero hne (div_ne_zero hCK (pow_ne_zero _ hpR))

/-- The integer polynomial certificates obtained from the Gaussian content proof. -/
theorem PK_coeff_den_elementary (hp : 2 ≤ p) (K i : ℕ) :
    ((PK p K).coeff i).den = 1 :=
  PK_coeff_den_of_content hp (content_coeff_elementary hp) K i

/-- The elementary second proof of irrationality, with Gaussian coefficient content
and the finite-sieve cubic cost `9/16`. -/
theorem irrational_xi_elementary (hp : 2 ≤ p) : Irrational (xi p) :=
  irrational_xi_elementary_of_content hp (content_coeff_elementary hp)

/-- The second proof's public theorem with the convergent series written explicitly.
`summable_term` and `hasSum_xi` certify convergence for every `p ≥ 2`. -/
theorem irrational_qzeta3_elementary (p : ℕ) (hp : 2 ≤ p) :
    Irrational (∑' n : ℕ, ((n : ℝ) + 1) ^ 2 / ((p : ℝ) ^ (n + 1) - 1)) := by
  simpa only [xi, term, Nat.cast_add, Nat.cast_one] using irrational_xi_elementary hp

end QZeta3
