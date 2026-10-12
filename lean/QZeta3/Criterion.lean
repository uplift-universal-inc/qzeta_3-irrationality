import QZeta3.Defs

/-!
# The irrationality criterion (proved)

The elementary principle behind §6 of the manuscript, in the same form as the one used for ζ(5)
(mo271/Zeta5, `Apery/Criterion.lean`):

> Let `ξ ∈ ℝ`.  Suppose `P_K ∈ ℚ[X]` has integer coefficients and degree `≤ K`, that
> `|P_K(ξ)| ≤ ε_K` for `K ≥ 1`, that `b^K ε_K → 0` for every positive integer `b`, and that
> `P_K(ξ) ≠ 0` for infinitely many `K`.  Then `ξ` is irrational.

Proof: if `ξ = a/b` then `b^K P_K(a/b)` is an integer; it is nonzero for infinitely many `K`
but tends to zero.
-/

open Polynomial Filter Topology Finset

namespace QZeta3

/-- `b^K P(a/b)` as an explicit integer, for `P ∈ ℚ[X]` with integer coefficients and
`deg P ≤ K`. -/
def intVal (P : ℚ[X]) (K : ℕ) (a b : ℤ) : ℤ :=
  ∑ i ∈ range (K + 1), (P.coeff i).num * a ^ i * b ^ (K - i)

theorem pow_mul_aeval_eq (P : ℚ[X]) (K : ℕ) (hdeg : P.natDegree ≤ K)
    (hint : ∀ i, (P.coeff i).den = 1) (a b : ℤ) (hb : b ≠ 0) :
    (b : ℝ) ^ K * aeval ((a : ℝ) / b) P = (intVal P K a b : ℝ) := by
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.mul_sum]
  unfold intVal
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hc : ((P.coeff i : ℚ) : ℝ) = ((P.coeff i).num : ℝ) := by
    have h := Rat.coe_int_num_of_den_eq_one (hint i)
    calc ((P.coeff i : ℚ) : ℝ) = (((P.coeff i).num : ℚ) : ℝ) := by rw [h]
      _ = ((P.coeff i).num : ℝ) := Rat.cast_intCast _
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  rw [Rat.smul_def, hc, div_pow, ← pow_sub_mul_pow (b : ℝ) hi']
  field_simp

/-- **Irrationality criterion.** -/
theorem irrational_of_poly_approx (ξ : ℝ) (P : ℕ → ℚ[X]) (hdeg : ∀ K, (P K).natDegree ≤ K)
    (hint : ∀ K i, ((P K).coeff i).den = 1) (ε : ℕ → ℝ)
    (hbound : ∀ K, 1 ≤ K → |aeval ξ (P K)| ≤ ε K)
    (hdecay : ∀ b : ℕ, 0 < b → Tendsto (fun K => (b : ℝ) ^ K * ε K) atTop (𝓝 0))
    (hnz : ∀ N, ∃ K, N ≤ K ∧ aeval ξ (P K) ≠ 0) : Irrational ξ := by
  rw [irrational_iff_ne_rational]
  intro a b hb hξ
  have hbpos : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have hev : ∀ᶠ K in atTop, (b.natAbs : ℝ) ^ K * ε K < 1 :=
    (hdecay b.natAbs hbpos).eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  obtain ⟨K, hKN, hK⟩ := hnz (max N 1)
  have hK1 : 1 ≤ K := le_trans (le_max_right _ _) hKN
  have hKN' : N ≤ K := le_trans (le_max_left _ _) hKN
  have hval := pow_mul_aeval_eq (P K) K (hdeg K) (hint K) a b hb
  rw [← hξ] at hval
  have habs : |(b : ℝ)| = (b.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hne : intVal (P K) K a b ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hval
    have hb' : (b : ℝ) ^ K ≠ 0 := pow_ne_zero _ (by exact_mod_cast hb)
    exact hK ((mul_eq_zero.mp hval).resolve_left hb')
  have h1 : (1 : ℝ) ≤ |(intVal (P K) K a b : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hne
  have h2 : |(intVal (P K) K a b : ℝ)| = (b.natAbs : ℝ) ^ K * |aeval ξ (P K)| := by
    rw [← hval, abs_mul, abs_pow, habs]
  have h3 := hN K hKN'
  have h4 : (b.natAbs : ℝ) ^ K * |aeval ξ (P K)| ≤ (b.natAbs : ℝ) ^ K * ε K :=
    mul_le_mul_of_nonneg_left (hbound K hK1) (by positivity)
  linarith

end QZeta3
