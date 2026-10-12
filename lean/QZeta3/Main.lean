import QZeta3.Criterion
import QZeta3.Asymptotics
import QZeta3.DenominatorSieve
import QZeta3.Frozen.Prop21
import QZeta3.Frozen.Prop31
import QZeta3.Frozen.Prop41
import QZeta3.Frozen.Prop51

/-!
# Assembly of the rationality contradiction (§6) — proved from the four propositions

* `PK p K = C_K p^{−e_K} Δ_K ∈ ℚ[X]`; by Propositions 3.1 and 4.1 its coefficients are integers
  (`PK_coeff_den`), its degree is `≤ K` (`natDegree_PK_le`).
* `abs_aeval_PK_le`: `|P_K(ξ_p)| ≤ ε_K` (Proposition 2.1).
* `irrational_xi`: `ξ_p` is irrational, by the criterion `QZeta3.irrational_of_poly_approx`,
  the decay `QZeta3.tendsto_pow_mul_epsK_of_cost`, the proved sieve growth bound
  `QZeta3.log_CK_rational_le` with cubic cost `107/192`, and Proposition 5.1.
  The sharper manuscript totient asymptotic is outside the formalized scope.

The gluing lemma `den_eq_one_of_coprime`: a rational number whose denominator is coprime to `p`
and which becomes an integer after multiplication by a power of `p` is an integer.  This replaces
the manuscript's remark "a rational number integral at every prime is an integer" together with
"`C_K` is coprime to `p`" (the latter is not needed in this form of the argument).
-/

open Polynomial Finset Filter Topology

namespace QZeta3

variable {p : ℕ}

/-- A rational number with denominator coprime to `p` which is integral after multiplication by
`p^m` is an integer. -/
theorem den_eq_one_of_coprime {r : ℚ} (hp : 0 < p) (hcop : Nat.Coprime r.den p) {m : ℕ}
    (h : (r * (p : ℚ) ^ m).den = 1) : r.den = 1 := by
  set n : ℤ := (r * (p : ℚ) ^ m).num with hn
  have hr : r = (n : ℚ) / ((p ^ m : ℕ) : ℤ) := by
    have h1 : ((r * (p : ℚ) ^ m).num : ℚ) = r * (p : ℚ) ^ m := Rat.coe_int_num_of_den_eq_one h
    have hp0 : ((p : ℚ) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne')
    rw [← hn] at h1
    push_cast
    rw [h1]
    field_simp
  have hdvd : (r.den : ℤ) ∣ ((p ^ m : ℕ) : ℤ) := by
    rw [hr, Rat.intCast_div_eq_divInt]
    exact Rat.den_dvd _ _
  have hdvd' : r.den ∣ p ^ m := by exact_mod_cast hdvd
  exact Nat.Coprime.eq_one_of_dvd (hcop.pow_right m) hdvd'

/-- `P_K = C_K p^{−e_K} Δ_K` (as an element of `ℚ[X]`). -/
noncomputable def PK (p K : ℕ) : ℚ[X] := Delta p K * C ((CK p K : ℚ) / (p : ℚ) ^ eK K)

theorem natDegree_PK_le (p K : ℕ) : (PK p K).natDegree ≤ K :=
  (Polynomial.natDegree_mul_C_le _ _).trans (natDegree_Delta_le p K)

/-- `P_K ∈ ℤ[X]` (Propositions 3.1 and 4.1). -/
theorem PK_coeff_den (hp : 2 ≤ p) (K i : ℕ) : ((PK p K).coeff i).den = 1 := by
  unfold PK
  rw [Polynomial.coeff_mul_C]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hrew : (Delta p K).coeff i * ((CK p K : ℚ) / (p : ℚ) ^ eK K) =
      (CK p K : ℚ) * ((Delta p K).coeff i / (p : ℚ) ^ eK K) := by ring
  rw [hrew]
  -- denominator coprime to `p` (Proposition 3.1)
  have hcop : Nat.Coprime ((CK p K : ℚ) * ((Delta p K).coeff i / (p : ℚ) ^ eK K)).den p := by
    have hdvd := Rat.mul_den_dvd (CK p K : ℚ) ((Delta p K).coeff i / (p : ℚ) ^ eK K)
    rw [Rat.den_intCast, one_mul] at hdvd
    exact Nat.Coprime.coprime_dvd_left hdvd (content_coeff hp K i)
  -- integral after multiplication by a power of `p` (Proposition 4.1)
  obtain ⟨m, hm⟩ := denominators_clear hp K i
  have hm' : ((CK p K : ℚ) * ((Delta p K).coeff i / (p : ℚ) ^ eK K) * (p : ℚ) ^ (m + eK K)).den
      = 1 := by
    have : (CK p K : ℚ) * ((Delta p K).coeff i / (p : ℚ) ^ eK K) * (p : ℚ) ^ (m + eK K) =
        (CK p K : ℚ) * (Delta p K).coeff i * (p : ℚ) ^ m := by
      have hpe : (p : ℚ) ^ eK K ≠ 0 := pow_ne_zero _ hp0
      calc (CK p K : ℚ) * ((Delta p K).coeff i / (p : ℚ) ^ eK K) * (p : ℚ) ^ (m + eK K)
          = (CK p K : ℚ) * (Delta p K).coeff i * (p : ℚ) ^ m *
              ((p : ℚ) ^ eK K / (p : ℚ) ^ eK K) := by rw [pow_add]; ring
        _ = (CK p K : ℚ) * (Delta p K).coeff i * (p : ℚ) ^ m := by
              rw [div_self hpe, mul_one]
    rw [this]
    exact hm
  exact den_eq_one_of_coprime (show 0 < p by omega) hcop hm'

theorem aeval_PK (p K : ℕ) (x : ℝ) :
    aeval x (PK p K) = DeltaR p K x * ((CK p K : ℝ) / (p : ℝ) ^ eK K) := by
  unfold PK DeltaR
  rw [aeval_mul, aeval_C, eq_ratCast]
  congr 1
  norm_cast

/-- `|P_K(ξ_p)| ≤ ε_K` (Proposition 2.1). -/
theorem abs_aeval_PK_le (hp : 2 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    |aeval (xi p) (PK p K)| ≤ epsK p K := by
  rw [aeval_PK, abs_mul]
  have hCK : (0 : ℝ) < CK p K := by exact_mod_cast CK_pos hp K
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hc : (0 : ℝ) ≤ (CK p K : ℝ) / (p : ℝ) ^ eK K := by positivity
  rw [abs_of_nonneg hc]
  have heps : epsK p K =
      ((K.factorial : ℝ) * (12 * (2 * (K : ℝ) - 1) ^ 2) ^ K * ((p : ℝ)⁻¹) ^ bK K) *
        ((CK p K : ℝ) / (p : ℝ) ^ eK K) := by
    unfold epsK
    rw [pow_add, inv_pow, inv_pow]
    ring
  rw [heps]
  exact mul_le_mul_of_nonneg_right (analytic_bound hp K hK) hc

/-- **Theorem 1.1.**  For every integer `p ≥ 2`, `ξ_p = ∑_{n ≥ 1} n²/(pⁿ − 1)` is irrational. -/
theorem irrational_xi (hp : 2 ≤ p) : Irrational (xi p) := by
  obtain ⟨c, hc⟩ := log_CK_rational_le hp
  refine irrational_of_poly_approx (xi p) (PK p) (natDegree_PK_le p) (PK_coeff_den hp) (epsK p)
    (abs_aeval_PK_le hp) (fun b hb => tendsto_pow_mul_epsK_of_cost hp (sub_pos.mp rational_cost_margin) hc b hb) ?_
  intro N
  obtain ⟨K, hKN, hne⟩ := frequently_ne_zero hp N
  refine ⟨K, hKN, ?_⟩
  rw [aeval_PK]
  have hCK : (CK p K : ℝ) ≠ 0 := by exact_mod_cast (CK_pos hp K).ne'
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  exact mul_ne_zero hne (div_ne_zero hCK (pow_ne_zero _ hpR))

end QZeta3
