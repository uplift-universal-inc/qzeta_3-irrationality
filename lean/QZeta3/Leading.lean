import QZeta3.Content
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-! # Exact algebra for the highest coefficient of the Hankel determinant. -/

open Polynomial Finset Matrix

namespace QZeta3

variable {p : ℕ}

theorem coeff_Delta_top_eq_det (p K : ℕ) :
    (Delta p K).coeff K = (hankelLin p K).det := by
  simpa [Delta] using Polynomial.coeff_det_X_add_C_card (hankelLin p K) (hankelConst p K)

theorem sum_Icc_eq_fin {R : Type*} [AddCommMonoid R] (K : ℕ) (f : ℕ → R) :
    ∑ a ∈ Icc 1 K, f a = ∑ i : Fin K, f (i.val + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Fin.sum_univ_castSucc, ih]
    rfl

theorem prod_Icc_eq_fin {R : Type*} [CommMonoid R] (K : ℕ) (f : ℕ → R) :
    ∏ a ∈ Icc 1 K, f a = ∏ i : Fin K, f (i.val + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.prod_Icc_succ_top (by omega), Fin.prod_univ_castSucc, ih]
    rfl

def nodes (p K : ℕ) (i : Fin K) : ℚ := (p : ℚ) ^ (i.val + 1)

theorem F_eq_nodal (p K : ℕ) :
    F p K = Lagrange.nodal univ (nodes p K) := by
  simpa [F, Lagrange.nodal, nodes] using prod_Icc_eq_fin K (fun a => X - C ((p : ℚ) ^ a))

theorem sum_card_Ioi_fin (K : ℕ) :
    ∑ i : Fin K, (Ioi i).card = K * (K - 1) / 2 := by
  have h := Equiv.sum_comp (Fin.revPerm (n := K)) (fun i : Fin K => i.val)
  calc
    _ = ∑ i : Fin K, (Fin.revPerm i).val := by
      apply sum_congr rfl
      intro i hi
      simp only [Fin.card_Ioi, Fin.revPerm_apply, Fin.val_rev]
      omega
    _ = ∑ i : Fin K, i.val := h
    _ = K * (K - 1) / 2 := by
      simpa only [Finset.sum_range] using Finset.sum_range_id K

theorem prod_derivative_nodal (K : ℕ) (v : Fin K → ℚ) :
    (∏ i, (derivative (Lagrange.nodal univ v)).eval (v i)) =
      (-1 : ℚ) ^ (K * (K - 1) / 2) * (Matrix.vandermonde v).det ^ 2 := by
  simp_rw [Lagrange.eval_nodal_derivative_eval_node_eq (mem_univ _), Lagrange.eval_nodal]
  have hsets (i : Fin K) : univ.erase i = {i}ᶜ := by ext j; simp
  simp_rw [hsets]
  rw [← Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun i j => v j - v i)]
  have h (i j : Fin K) : (v i - v j) * (v j - v i) = -1 * (v j - v i) ^ 2 := by ring
  simp_rw [h, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow,
    Finset.prod_pow_eq_pow_sum]
  rw [sum_card_Ioi_fin, Matrix.det_vandermonde]

noncomputable def linWeight (p K : ℕ) (i : Fin K) : ℚ :=
  -nrm p K / (nodes p K i * (derivative (F p K)).eval (nodes p K i))

theorem hankelLin_factor (p K : ℕ) :
    hankelLin p K = (Matrix.vandermonde (nodes p K))ᵀ *
      Matrix.diagonal (linWeight p K) * Matrix.vandermonde (nodes p K) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  simp only [hankelLin, Matrix.of_apply, mLin, sum_Icc_eq_fin, mul_neg,
    Finset.mul_sum, ← Finset.sum_neg_distrib, Matrix.transpose_apply,
    Matrix.vandermonde_apply]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [res, linWeight, nodes, pow_mul, pow_add, div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem nodes_injective (hp : 2 ≤ p) (K : ℕ) : Function.Injective (nodes p K) := by
  intro i j hij
  have hp1 : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have hpow := (pow_right_strictMono₀ hp1).injective hij
  exact Fin.ext (by omega)

theorem derivative_F_node_ne_zero (hp : 2 ≤ p) (K : ℕ) (i : Fin K) :
    (derivative (F p K)).eval (nodes p K i) ≠ 0 := by
  rw [F_eq_nodal]
  have h := Lagrange.nodalWeight_ne_zero (nodes_injective hp K).injOn (mem_univ i)
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ i)] at h
  intro hz
  change (derivative (Lagrange.nodal univ (nodes p K))).eval (nodes p K i) = 0 at hz
  exact h (by rw [hz, _root_.inv_zero])

theorem linWeight_ne_zero (hp : 2 ≤ p) (K : ℕ) (i : Fin K) : linWeight p K i ≠ 0 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  apply div_ne_zero
  · exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hp0))
  · exact mul_ne_zero (pow_ne_zero _ hp0) (derivative_F_node_ne_zero hp K i)

theorem det_hankelLin_ne_zero (hp : 2 ≤ p) (K : ℕ) : (hankelLin p K).det ≠ 0 := by
  rw [hankelLin_factor, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal]
  exact mul_ne_zero
    (mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr (nodes_injective hp K))
      (Finset.prod_ne_zero_iff.mpr (fun i hi => linWeight_ne_zero hp K i)))
    (Matrix.det_vandermonde_ne_zero_iff.mpr (nodes_injective hp K))

theorem prod_nodes (p K : ℕ) : ∏ i : Fin K, nodes p K i = (p : ℚ) ^ AK K := by
  unfold nodes
  rw [← prod_Icc_eq_fin K (fun a => (p : ℚ) ^ a)]
  rw [Finset.prod_pow_eq_pow_sum, sum_Icc_id_eq_AK]

theorem neg_nrm_pow (p K : ℕ) : (-nrm p K) ^ K = (p : ℚ) ^ (AK K * K) := by
  have heven : Even ((K + 1) * K) := by simpa [Nat.mul_comm] using Nat.even_mul_succ_self K
  calc
    (-nrm p K) ^ K = ((-1 : ℚ) ^ (K + 1) * (p : ℚ) ^ AK K) ^ K := by
      congr 1
      simp [nrm, pow_succ]
    _ = (p : ℚ) ^ (AK K * K) := by
      rw [mul_pow, ← pow_mul, heven.neg_one_pow, one_mul, ← pow_mul]

theorem det_hankelLin_eq (hp : 2 ≤ p) (K : ℕ) :
    (hankelLin p K).det = (-1) ^ (K * (K - 1) / 2) * (p : ℚ) ^ eK K := by
  by_cases hK : K = 0
  · subst K
    simp [hankelLin, eK, AK]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hv0 := Matrix.det_vandermonde_ne_zero_iff.mpr (nodes_injective hp K)
  have hprod : ∏ i : Fin K, (derivative (F p K)).eval (nodes p K i) =
      (-1 : ℚ) ^ (K * (K - 1) / 2) * (Matrix.vandermonde (nodes p K)).det ^ 2 := by
    rw [F_eq_nodal]
    exact prod_derivative_nodal K (nodes p K)
  have hexp : AK K * K = AK K + eK K := by
    unfold eK
    have : K = 1 + (K - 1) := by omega
    nlinarith
  have hsign : ((-1 : ℚ) ^ (K * (K - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [hankelLin_factor, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal]
  simp_rw [linWeight, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  rw [Finset.prod_const, card_univ, Fintype.card_fin, prod_nodes, hprod, neg_nrm_pow,
    hexp, pow_add]
  field_simp
  nlinarith [hsign]

theorem leading_coeff_proved (hp : 2 ≤ p) (K : ℕ) :
    (Delta p K).coeff K = (-1) ^ (K * (K - 1) / 2) * (p : ℚ) ^ eK K := by
  rw [coeff_Delta_top_eq_det, det_hankelLin_eq hp]

end QZeta3
