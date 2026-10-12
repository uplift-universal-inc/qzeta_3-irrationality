import QZeta3.Leading

/-! # Finite interpolation identities for the moving denominator. -/

open Polynomial Finset

namespace QZeta3

variable {p : ℕ}

theorem F_eval_node (p K : ℕ) (i : Fin K) : (F p K).eval (nodes p K i) = 0 := by
  rw [F_eq_nodal]
  exact Lagrange.eval_nodal_at_node (mem_univ i)

theorem rem_eval_node (p K : ℕ) (f : ℚ[X]) (i : Fin K) :
    (f %ₘ F p K).eval (nodes p K i) = f.eval (nodes p K i) := by
  exact Polynomial.eval₂_modByMonic_eq_self_of_root (F_eval_node p K i)

theorem rem_degree_lt (p K : ℕ) (f : ℚ[X]) : (f %ₘ F p K).degree < K := by
  have h := Polynomial.degree_modByMonic_lt f (F_monic p K)
  rwa [Polynomial.degree_eq_natDegree (F_monic p K).ne_zero, F_natDegree] at h

/-- A polynomial's residue sum is the top coefficient of its remainder modulo `F_K`. -/
theorem residue_sum_eq_rem_coeff (hp : 2 ≤ p) (K : ℕ) (f : ℚ[X]) :
    (∑ i : Fin K, f.eval (nodes p K i) / (derivative (F p K)).eval (nodes p K i)) =
      (f %ₘ F p K).coeff (K - 1) := by
  have h := Lagrange.coeff_eq_sum (s := univ) (nodes_injective hp K).injOn
    (P := f %ₘ F p K) (by simpa using rem_degree_lt p K f)
  simp only [card_univ, Fintype.card_fin, rem_eval_node] at h
  rw [h]
  apply sum_congr rfl
  intro i hi
  rw [F_eq_nodal, Lagrange.eval_nodal_derivative_eval_node_eq (mem_univ i), Lagrange.eval_nodal]

theorem residue_sum_Icc_eq_rem_coeff (hp : 2 ≤ p) (K : ℕ) (f : ℚ[X]) :
    (∑ a ∈ Icc 1 K, f.eval ((p : ℚ) ^ a) / (derivative (F p K)).eval ((p : ℚ) ^ a)) =
      (f %ₘ F p K).coeff (K - 1) := by
  rw [sum_Icc_eq_fin]
  exact residue_sum_eq_rem_coeff hp K f

/-- Polynomial partial fractions, with the denominator cleared. -/
theorem partial_fraction_polynomial (hp : 2 ≤ p) (K : ℕ) (f : ℚ[X]) :
    f = F p K * (f /ₘ F p K) +
      ∑ i : Fin K, C (f.eval (nodes p K i) / (derivative (F p K)).eval (nodes p K i)) *
        Lagrange.nodal (univ.erase i) (nodes p K) := by
  have h := Lagrange.eq_interpolate (s := univ) (nodes_injective hp K).injOn
    (f := f %ₘ F p K) (by simpa using rem_degree_lt p K f)
  rw [Lagrange.interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C] at h
  have hr : f %ₘ F p K =
      ∑ i : Fin K, C (f.eval (nodes p K i) / (derivative (F p K)).eval (nodes p K i)) *
        Lagrange.nodal (univ.erase i) (nodes p K) := by
    rw [h]
    apply sum_congr rfl
    intro i hi
    rw [← Lagrange.nodal_erase_eq_nodal_div (mem_univ i), rem_eval_node,
      Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ i), ← F_eq_nodal]
    simp only [div_eq_mul_inv, map_mul]
    ring
  rw [← hr, add_comm, Polynomial.modByMonic_add_div]

theorem partial_fraction_eval {E : Type*} [Field E] (hp : 2 ≤ p) (K : ℕ)
    (f : ℚ[X]) (φ : ℚ →+* E) (x : E) (hx : ∀ i : Fin K, x ≠ φ (nodes p K i)) :
    f.eval₂ φ x / (F p K).eval₂ φ x = (f /ₘ F p K).eval₂ φ x +
      ∑ i : Fin K, φ (f.eval (nodes p K i) / (derivative (F p K)).eval (nodes p K i)) /
        (x - φ (nodes p K i)) := by
  have hF : (F p K).eval₂ φ x ≠ 0 := by
    rw [F_eq_nodal]
    simp only [Lagrange.nodal, Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => sub_ne_zero.mpr (hx i))
  have hnode (i : Fin K) :
      (Lagrange.nodal (univ.erase i) (nodes p K)).eval₂ φ x =
        (F p K).eval₂ φ x / (x - φ (nodes p K i)) := by
    apply (eq_div_iff (sub_ne_zero.mpr (hx i))).mpr
    rw [F_eq_nodal, Lagrange.nodal_eq_mul_nodal_erase (mem_univ i)]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    ring
  have h := congrArg (fun g : ℚ[X] => g.eval₂ φ x) (partial_fraction_polynomial hp K f)
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_C, hnode] at h
  apply (div_eq_iff hF).mpr
  rw [h, add_mul, Finset.sum_mul]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i hi
    ring

theorem partial_fraction_real (hp : 2 ≤ p) (K k : ℕ) (x : ℝ)
    (hx : ∀ a ∈ Icc 1 K, x ≠ (p : ℝ) ^ a) :
    x ^ k / (F p K).eval₂ (Rat.castHom ℝ) x =
      (X ^ k /ₘ F p K).eval₂ (Rat.castHom ℝ) x +
      ∑ a ∈ Icc 1 K, (res p K k a : ℝ) / (x - (p : ℝ) ^ a) := by
  have hx' (i : Fin K) : x ≠ (Rat.castHom ℝ) (nodes p K i) := by
    simpa [nodes] using hx (i.val + 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
  have h := partial_fraction_eval hp K (X ^ k) (Rat.castHom ℝ) x hx'
  simp only [Polynomial.eval₂_X_pow, Polynomial.eval_pow, Polynomial.eval_X] at h
  rw [h]
  congr 1
  rw [sum_Icc_eq_fin]
  apply sum_congr rfl
  intro i hi
  simp [nodes, res, pow_mul]

theorem mLin_zero (hp : 2 ≤ p) (K : ℕ) (hK : 0 < K) :
    mLin p K 0 = ((F p K).eval 0)⁻¹ := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hx (i : Fin K) : (0 : ℚ) ≠ (RingHom.id ℚ) (nodes p K i) :=
    (pow_ne_zero _ hp0).symm
  have hdiv : (1 : ℚ[X]) /ₘ F p K = 0 := by
    apply (Polynomial.divByMonic_eq_zero_iff (F_monic p K)).mpr
    rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree (F_monic p K).ne_zero,
      F_natDegree]
    exact_mod_cast hK
  have h := partial_fraction_eval hp K 1 (RingHom.id ℚ) 0 hx
  simp only [hdiv, Polynomial.eval₂_one, Polynomial.eval₂_zero, Polynomial.eval_one,
    RingHom.id_apply, zero_add, zero_sub, div_neg, one_div, Polynomial.eval₂_id] at h
  rw [mLin, sum_Icc_eq_fin]
  simpa [res, nodes, ← Finset.sum_neg_distrib] using h.symm

theorem denominator_normalization (hp : 2 ≤ p) (K : ℕ) (x : ℝ) :
    (∏ a ∈ Icc 1 K, (1 - ((p : ℝ)⁻¹) ^ a * x)) =
      (1 / (nrm p K : ℝ)) * (F p K).eval₂ (Rat.castHom ℝ) x := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hn0 : (nrm p K : ℝ) ≠ 0 := by
    simp only [nrm, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hp0)
  have hn : (nrm p K : ℝ) = ∏ a ∈ Icc 1 K, -((p : ℝ) ^ a) := by
    simp only [nrm, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    simp only [Finset.prod_neg, Nat.card_Icc]
    simp only [Nat.add_sub_cancel]
    congr 1
    rw [Finset.prod_pow_eq_pow_sum, sum_Icc_id_eq_AK]
  have hmul : (nrm p K : ℝ) * (∏ a ∈ Icc 1 K, (1 - ((p : ℝ)⁻¹) ^ a * x)) =
      (F p K).eval₂ (Rat.castHom ℝ) x := by
    rw [hn, ← Finset.prod_mul_distrib]
    simp only [F, Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Rat.coe_castHom, Rat.cast_pow, Rat.cast_natCast]
    apply Finset.prod_congr rfl
    intro a ha
    rw [inv_pow]
    field_simp
    ring
  apply (mul_left_cancel₀ hn0)
  rw [hmul]
  field_simp

end QZeta3
