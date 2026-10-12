import QZeta3.ContentProof

/-! # A uniform base-power denominator for individual residue summands. -/

open Polynomial Finset

namespace QZeta3

variable {p : ℕ}

theorem pow_div_difference_mem_of_lt (hp : 2 ≤ p) (N a b : ℕ)
    (hab : a < b) (hb : b ≤ N) :
    (p : ℚ) ^ N / ((p : ℚ) ^ a - (p : ℚ) ^ b) ∈ baseIntegral p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hd : 0 < b - a := by omega
  have hpow : 1 ≤ p ^ (b - a) := one_le_pow₀ (show 1 ≤ p by omega)
  have hint := intCast_div_mem_baseIntegral (-((p : ℤ) ^ (N - a)))
    ((p ^ (b - a) - 1 : ℕ) : ℤ)
    (by simpa using pow_sub_one_coprime p (b - a) (by omega) hd)
  have heq : (p : ℚ) ^ N / ((p : ℚ) ^ a - (p : ℚ) ^ b) =
      (-((p : ℤ) ^ (N - a)) : ℤ) / ((p ^ (b - a) - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hpow]
    have hbexp : (p : ℚ) ^ b = (p : ℚ) ^ a * (p : ℚ) ^ (b - a) := by
      rw [← pow_add, Nat.add_sub_of_le (by omega)]
    have hNexp : (p : ℚ) ^ N = (p : ℚ) ^ a * (p : ℚ) ^ (N - a) := by
      rw [← pow_add, Nat.add_sub_of_le (by omega)]
    rw [hbexp, hNexp]
    field_simp
    rw [show (1 - (p : ℚ) ^ (b - a)) = -(-1 + (p : ℚ) ^ (b - a)) by ring, div_neg]
    congr 2
    ring
  rw [heq]
  exact hint

theorem pow_div_difference_mem (hp : 2 ≤ p) (N a b : ℕ)
    (ha : a ≤ N) (hb : b ≤ N) (hab : a ≠ b) :
    (p : ℚ) ^ N / ((p : ℚ) ^ a - (p : ℚ) ^ b) ∈ baseIntegral p := by
  rcases lt_or_gt_of_ne hab with hab | hab
  · exact pow_div_difference_mem_of_lt hp N a b hab hb
  · have h := (baseIntegral p).neg_mem (pow_div_difference_mem_of_lt hp N b a hab ha)
    convert h using 1
    rw [← neg_sub ((p : ℚ) ^ b), div_neg]

theorem derivative_F_eval_eq_prod (p K a : ℕ) (ha : a ∈ Icc 1 K) :
    (derivative (F p K)).eval ((p : ℚ) ^ a) =
      ∏ b ∈ (Icc 1 K).erase a, ((p : ℚ) ^ a - (p : ℚ) ^ b) := by
  change (derivative (Lagrange.nodal (Icc 1 K) (fun b => (p : ℚ) ^ b))).eval
    ((p : ℚ) ^ a) = _
  rw [Lagrange.eval_nodal_derivative_eval_node_eq ha, Lagrange.eval_nodal]

theorem derivative_scaled_inv_mem (hp : 2 ≤ p) (K a : ℕ) (ha : a ∈ Icc 1 K) :
    (p : ℚ) ^ (K * (K - 1)) / (derivative (F p K)).eval ((p : ℚ) ^ a) ∈
      baseIntegral p := by
  have hprod : (∏ b ∈ (Icc 1 K).erase a,
      (p : ℚ) ^ K / ((p : ℚ) ^ a - (p : ℚ) ^ b)) ∈ baseIntegral p := by
    apply (baseIntegral p).prod_mem
    intro b hb
    exact pow_div_difference_mem hp K a b (mem_Icc.mp ha).2
      (mem_Icc.mp (mem_erase.mp hb).2).2 (mem_erase.mp hb).1.symm
  have hcard : ((Icc 1 K).erase a).card = K - 1 := by
    rw [card_erase_of_mem ha, Nat.card_Icc]
    simp
  rw [Finset.prod_div_distrib, Finset.prod_const, hcard, ← pow_mul,
    ← derivative_F_eval_eq_prod p K a ha] at hprod
  exact hprod

theorem residue_scaled_mem (hp : 2 ≤ p) (K k a : ℕ) (ha : a ∈ Icc 1 K) :
    (p : ℚ) ^ (K * K + K) * (res p K k a / (p : ℚ) ^ a) ∈ baseIntegral p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hK : 0 < K := by have := mem_Icc.mp ha; omega
  have hKa : a ≤ K := (mem_Icc.mp ha).2
  have hexp : K * K + K = K * (K - 1) + (K + K - a) + a := by
    have h1 : K - 1 + 1 = K := by omega
    have h2 : K + K - a + a = K + K := by omega
    nlinarith
  have h := (baseIntegral p).mul_mem (derivative_scaled_inv_mem hp K a ha)
    ((baseIntegral p).pow_mem (natCast_mem (baseIntegral p) p) (K + K - a + a * k))
  convert h using 1
  unfold res
  rw [hexp, pow_add, pow_add, pow_add]
  field_simp

end QZeta3
