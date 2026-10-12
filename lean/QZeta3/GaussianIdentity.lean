import QZeta3.DividedDifferences

/-! # Gaussian binomial evaluation of geometric divided differences

The Gaussian coefficients are defined by their integral Pascal recurrence in
rectangle coordinates: `gaussianRectangle p k t = [k+t choose k]_p`.
-/

open Polynomial Finset

namespace QZeta3

variable {p : ℕ}

/-- The Gaussian binomial coefficient `[k+t choose k]_p`, defined by the
standard recurrence. This definition visibly takes values in the natural numbers. -/
def gaussianRectangle (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | k + 1, t + 1 => gaussianRectangle p k (t + 1) +
      p ^ (k + 1) * gaussianRectangle p (k + 1) t
termination_by k t => k + t

/-- Gaussian binomial coefficients, zero above the diagonal. -/
def gaussianBinomial (p n k : ℕ) : ℕ :=
  if k ≤ n then gaussianRectangle p k (n - k) else 0

@[simp] theorem gaussianBinomial_zero_right (p n : ℕ) : gaussianBinomial p n 0 = 1 := by
  simp [gaussianBinomial, gaussianRectangle]

@[simp] theorem gaussianBinomial_diagonal (p n : ℕ) : gaussianBinomial p n n = 1 := by
  cases n <;> simp [gaussianBinomial, gaussianRectangle]

/-- The usual Gaussian Pascal relation in the interior of the triangle. -/
theorem gaussianBinomial_pascal (p n k : ℕ) (hk : k + 1 ≤ n) :
    gaussianBinomial p (n + 1) (k + 1) =
      gaussianBinomial p n k + p ^ (k + 1) * gaussianBinomial p n (k + 1) := by
  simp only [gaussianBinomial, ite_eq_left (show k + 1 ≤ n + 1 by omega),
    ite_eq_left (show k ≤ n by omega), ite_eq_left hk]
  have hexp : n + 1 - (k + 1) = (n - (k + 1)) + 1 := by omega
  rw [hexp, gaussianRectangle]
  congr 1
  congr 1
  omega

/-- Monomial barycentric divided difference at `p,p²,…,pᴷ`. -/
noncomputable def geometricResidue (p K d : ℕ) : ℚ :=
  ∑ a ∈ Icc 1 K, ((p : ℚ) ^ a) ^ d /
    (derivative (F p K)).eval ((p : ℚ) ^ a)

theorem geometricResidue_eq_rem (hp : 2 ≤ p) (K d : ℕ) :
    geometricResidue p K d = ((X ^ d : ℚ[X]) %ₘ F p K).coeff (K - 1) := by
  simpa [geometricResidue] using residue_sum_Icc_eq_rem_coeff hp K (X ^ d)

theorem geometricResidue_low (hp : 2 ≤ p) (K d : ℕ) (hd : d < K - 1) :
    geometricResidue p K d = 0 := by
  rw [geometricResidue_eq_rem hp]
  have hdeg : (X ^ d : ℚ[X]).degree < (F p K).degree := by
    rw [degree_X_pow, degree_eq_natDegree (F_monic p K).ne_zero, F_natDegree]
    exact_mod_cast (show d < K by omega)
  rw [modByMonic_eq_self_iff (F_monic p K) |>.mpr hdeg]
  simp [coeff_X_pow, show K - 1 ≠ d by omega]

theorem geometricResidue_top (hp : 2 ≤ p) (K : ℕ) (hK : 0 < K) :
    geometricResidue p K (K - 1) = 1 := by
  rw [geometricResidue_eq_rem hp]
  have hdeg : (X ^ (K - 1) : ℚ[X]).degree < (F p K).degree := by
    rw [degree_X_pow, degree_eq_natDegree (F_monic p K).ne_zero, F_natDegree]
    exact_mod_cast (show K - 1 < K by omega)
  rw [modByMonic_eq_self_iff (F_monic p K) |>.mpr hdeg]
  simp

theorem geometricResidue_one (p d : ℕ) : geometricResidue p 1 d = (p : ℚ) ^ d := by
  simp [geometricResidue, F]

theorem F_succ_geometric (p K : ℕ) :
    F p (K + 1) = F p K * (X - C ((p : ℚ) ^ (K + 1))) := by
  unfold F
  rw [Finset.prod_Icc_succ_top (by omega)]

theorem derivative_F_succ_old_node (p K a : ℕ) (ha : a ∈ Icc 1 K) :
    (derivative (F p (K + 1))).eval ((p : ℚ) ^ a) =
      (derivative (F p K)).eval ((p : ℚ) ^ a) *
        ((p : ℚ) ^ a - (p : ℚ) ^ (K + 1)) := by
  have hn : (F p K).eval ((p : ℚ) ^ a) = 0 := by
    have := F_eval_node p K (⟨a - 1, by have := (mem_Icc.mp ha); omega⟩ : Fin K)
    simpa only [nodes, Nat.sub_add_cancel (mem_Icc.mp ha).1] using this
  rw [F_succ_geometric, derivative_mul]
  simp [hn]

theorem geometricResidue_step (hp : 2 ≤ p) (K d : ℕ) :
    geometricResidue p (K + 1) (d + 1) =
      geometricResidue p K d + (p : ℚ) ^ (K + 1) * geometricResidue p (K + 1) d := by
  have hp1 : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have hdiff (a : ℕ) (ha : a ∈ Icc 1 K) :
      (p : ℚ) ^ a - (p : ℚ) ^ (K + 1) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact (pow_right_strictMono₀ hp1).injective.ne (by have := (mem_Icc.mp ha); omega)
  have hsub : geometricResidue p (K + 1) (d + 1) -
      (p : ℚ) ^ (K + 1) * geometricResidue p (K + 1) d = geometricResidue p K d := by
    unfold geometricResidue
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hlast : ((p : ℚ) ^ (K + 1)) ^ (d + 1) /
        (derivative (F p (K + 1))).eval ((p : ℚ) ^ (K + 1)) -
        (p : ℚ) ^ (K + 1) * (((p : ℚ) ^ (K + 1)) ^ d /
        (derivative (F p (K + 1))).eval ((p : ℚ) ^ (K + 1))) = 0 := by
      rw [pow_succ]
      ring
    rw [hlast, add_zero]
    apply Finset.sum_congr rfl
    intro a ha
    rw [derivative_F_succ_old_node p K a ha, pow_succ]
    have hz := hdiff a ha
    field_simp
  linarith

/-- The complete homogeneous form of the Gaussian-binomial divided difference. -/
theorem geometricResidue_gaussianRectangle (hp : 2 ≤ p) (k t : ℕ) :
    geometricResidue p (k + 1) (k + t) =
      (p : ℚ) ^ t * (gaussianRectangle p k t : ℚ) := by
  induction k generalizing t with
  | zero => simp [gaussianRectangle, geometricResidue_one]
  | succ k ih =>
    induction t with
    | zero =>
      simpa [gaussianRectangle] using geometricResidue_top hp (k + 2) (by omega)
    | succ t iht =>
      rw [show k + 1 + (t + 1) = (k + 1 + t) + 1 by omega,
        geometricResidue_step hp (k + 1) (k + 1 + t)]
      rw [show k + 1 + t = k + (t + 1) by omega, ih (t + 1)]
      have iht' : geometricResidue p (k + 1 + 1) (k + (t + 1)) =
          (p : ℚ) ^ t * (gaussianRectangle p (k + 1) t : ℚ) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using iht
      rw [iht']
      simp only [gaussianRectangle, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      rw [pow_succ, pow_succ (p : ℚ) (k + 1)]
      ring

/-- The geometric divided-difference identity in conventional Gaussian notation. -/
theorem gaussian_residue_identity (hp : 2 ≤ p) (K d : ℕ) (hK : 0 < K)
    (hd : K - 1 ≤ d) :
    (∑ a ∈ Icc 1 K, ((p : ℚ) ^ a) ^ d /
      (derivative (F p K)).eval ((p : ℚ) ^ a)) =
      (p : ℚ) ^ (d - (K - 1)) * (gaussianBinomial p d (K - 1) : ℚ) := by
  have h := geometricResidue_gaussianRectangle hp (K - 1) (d - (K - 1))
  simpa [geometricResidue, gaussianBinomial, hd, Nat.sub_add_cancel (show 1 ≤ K by omega),
    Nat.add_sub_of_le hd] using h

/-- Every nonnegative monomial divided difference is an integer. -/
theorem gaussian_residue_integral (hp : 2 ≤ p) (K d : ℕ) :
    ∃ z : ℤ, (∑ a ∈ Icc 1 K, ((p : ℚ) ^ a) ^ d /
      (derivative (F p K)).eval ((p : ℚ) ^ a)) = z := by
  by_cases hK : K = 0
  · subst K
    exact ⟨0, by simp⟩
  by_cases hd : d < K - 1
  · exact ⟨0, geometricResidue_low hp K d hd⟩
  · refine ⟨(p : ℤ) ^ (d - (K - 1)) * gaussianBinomial p d (K - 1), ?_⟩
    rw [gaussian_residue_identity hp K d (by omega) (by omega)]
    norm_cast

/-- The exceptional exponent `d = -1`, needed for the constant moment. -/
theorem geometricResidue_reciprocal (hp : 2 ≤ p) (K : ℕ) (hK : 0 < K) :
    (∑ a ∈ Icc 1 K, ((p : ℚ) ^ a)⁻¹ /
      (derivative (F p K)).eval ((p : ℚ) ^ a)) = -((F p K).eval 0)⁻¹ := by
  have h := mLin_zero hp K hK
  have hs : mLin p K 0 = -(∑ a ∈ Icc 1 K, ((p : ℚ) ^ a)⁻¹ /
      (derivative (F p K)).eval ((p : ℚ) ^ a)) := by
    unfold mLin
    congr 1
    apply sum_congr rfl
    intro a ha
    simp only [res, mul_zero, pow_zero]
    simp only [div_eq_mul_inv]
    ring
  rw [hs] at h
  linarith

end QZeta3
