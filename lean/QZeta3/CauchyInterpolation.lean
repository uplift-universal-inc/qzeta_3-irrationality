import QZeta3.CauchyFunctional
import QZeta3.NonvanishingAlgebra
import QZeta3.MomentDecay

open Polynomial Finset Filter Topology

namespace QZeta3

variable {p : ℕ}

/-- Divided difference of a monomial, as a polynomial in the support variable. -/
noncomputable def monomialDivDiff (k : ℕ) (z : ℝ) : ℝ[X] :=
  ∑ j ∈ range k, C (z ^ (k - 1 - j)) * X ^ j

/-- Divided difference `(Q(z)-Q(x))/(z-x)`, with exact polynomial division. -/
noncomputable def realDivDiff (Q : ℝ[X]) (z : ℝ) : ℝ[X] :=
  ∑ k ∈ Q.support, Q.coeff k • monomialDivDiff k z

/-- Polynomial part of the product of the Cauchy transform and `Q`. -/
noncomputable def cauchyPolynomialPart (p : ℕ) (Q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Q.support, Q.coeff k •
    ∑ j ∈ range k, C (mu p j : ℝ) * X ^ (k - 1 - j)

theorem eval_monomialDivDiff (k : ℕ) (z x : ℝ) :
    (monomialDivDiff k z).eval x =
      ∑ j ∈ range k, z ^ (k - 1 - j) * x ^ j := by
  simp only [monomialDivDiff, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem monomialDivDiff_identity (k : ℕ) (z x : ℝ) :
    (z - x) * (monomialDivDiff k z).eval x = z ^ k - x ^ k := by
  rw [eval_monomialDivDiff]
  have h := geom_sum₂_mul x z k
  simp_rw [mul_comm (x ^ _) (z ^ _)] at h
  nlinarith

theorem realDivDiff_identity (Q : ℝ[X]) (z x : ℝ) :
    (z - x) * (realDivDiff Q z).eval x = Q.eval z - Q.eval x := by
  simp only [realDivDiff, Polynomial.eval_finsetSum, Polynomial.eval_smul,
    smul_eq_mul, Finset.mul_sum]
  have hterm : ∀ k, (z - x) * (Q.coeff k * (monomialDivDiff k z).eval x) =
      Q.coeff k * (z ^ k - x ^ k) := by
    intro k
    rw [← mul_assoc, mul_comm (z-x) (Q.coeff k), mul_assoc, monomialDivDiff_identity]
  simp_rw [hterm, mul_sub]
  rw [Finset.sum_sub_distrib]
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def]

theorem numeratorFunctional_zero_monomial (hp : 2 ≤ p) (j : ℕ) :
    numeratorFunctional hp 0 (X ^ j) = (mu p j : ℝ) := by
  simpa [numeratorFunctional, DK] using Lfun_pow hp j

theorem cauchyPolynomialPart_eval (hp : 2 ≤ p) (Q : ℝ[X]) (z : ℝ) :
    (cauchyPolynomialPart p Q).eval z = numeratorFunctional hp 0 (realDivDiff Q z) := by
  simp only [cauchyPolynomialPart, realDivDiff, monomialDivDiff, Polynomial.eval_finsetSum,
    Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Polynomial.smul_eq_C_mul, map_smul, numeratorFunctional_zero_monomial hp]
  simp [mul_comm]

/-- Orthogonality to monomials extends to every polynomial of lower degree. -/
theorem orthogonal_to_polynomial (L : ℝ[X] →ₗ[ℝ] ℝ) (Q H : ℝ[X]) {n : ℕ}
    (horth : ∀ j : Fin n, L (X ^ j.val * Q) = 0) (hH : H.natDegree < n) :
    L (H * Q) = 0 := by
  conv_lhs => rw [← Polynomial.sum_monomial_eq H]
  simp only [Polynomial.sum_def, Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hjn : j < n := (Polynomial.le_natDegree_of_mem_supp j hj).trans_lt hH
  rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.smul_eq_C_mul,
    smul_mul_assoc, map_smul, horth ⟨j, hjn⟩, smul_zero]

/-- The real polynomial represented by the moving denominator. -/
noncomputable def realDenominator (p n : ℕ) : ℝ[X] :=
  C (1 / (nrm p n : ℝ)) * (F p n).map (Rat.castHom ℝ)

theorem realDenominator_eval (hp : 2 ≤ p) (n : ℕ) (x : ℝ) :
    (realDenominator p n).eval x = DK p n x := by
  simp only [realDenominator, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map]
  exact (denominator_normalization hp n x).symm

theorem realDenominator_natDegree_le (p n : ℕ) :
    (realDenominator p n).natDegree ≤ n := by
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  exact (Polynomial.natDegree_map_le).trans (le_of_eq (F_natDegree p n))

theorem realDenominator_eval_node (hp : 2 ≤ p) {n a : ℕ} (ha : a ∈ Icc 1 n) :
    (realDenominator p n).eval ((p : ℝ)^a) = 0 := by
  rw [realDenominator_eval hp, DK]
  apply Finset.prod_eq_zero ha
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  simp [inv_pow, pow_ne_zero a hp0]

/-- At an exterior node, the denominator divided by `(z-X)` has degree below `n`. -/
theorem denominator_node_quotient (hp : 2 ≤ p) {n a : ℕ} (ha : a ∈ Icc 1 n) :
    ∃ H : ℝ[X], H.natDegree < n ∧
      ∀ x : ℝ, DK p n x = ((p : ℝ)^a - x) * H.eval x := by
  let z : ℝ := (p : ℝ)^a
  let D := realDenominator p n
  let H := -(D /ₘ (X - C z))
  have hrem : D %ₘ (X - C z) = 0 := by
    rw [Polynomial.modByMonic_X_sub_C_eq_C_eval]
    change C ((realDenominator p n).eval ((p : ℝ)^a)) = 0
    rw [realDenominator_eval_node hp ha, Polynomial.C_0]
  have hdiv : (X - C z) * (D /ₘ (X - C z)) = D := by
    have h := Polynomial.modByMonic_add_div D (X - C z)
    simpa [hrem] using h
  have hdegree : H.natDegree < n := by
    dsimp [H]
    rw [Polynomial.natDegree_neg, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C z),
      Polynomial.natDegree_X_sub_C]
    have hd : D.natDegree ≤ n := realDenominator_natDegree_le p n
    have hn : 0 < n := by have := (Finset.mem_Icc.mp ha); omega
    omega
  refine ⟨H, hdegree, ?_⟩
  intro x
  have he := congrArg (Polynomial.eval x) hdiv
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at he
  rw [← realDenominator_eval hp]
  dsimp [H]
  simp only [Polynomial.eval_neg]
  change D.eval x = (z - x) * -((D /ₘ (X - C z)).eval x)
  nlinarith

/-- Every fixed polynomial multiplier has a unique polynomial part and a
remainder tending to zero at infinity. -/
theorem tendsto_cauchyPolynomialPart_error (hp : 2 ≤ p) (Q : ℝ[X]) :
    Tendsto (fun z => cauchyF p z * Q.eval z - (cauchyPolynomialPart p Q).eval z)
      atTop (𝓝 0) := by
  have heq : ∀ z : ℝ,
      cauchyF p z * Q.eval z - (cauchyPolynomialPart p Q).eval z =
      ∑ k ∈ Q.support, Q.coeff k *
        (cauchySeries p z * z ^ k - momentPolynomial p k z) := by
    intro z
    simp only [cauchyPolynomialPart, Polynomial.eval_finsetSum, Polynomial.eval_smul,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      smul_eq_mul, momentPolynomial_eq_mu, mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    change cauchySeries p z * (Q.coeff k * z ^ k) = _
    ring
  have h := tendsto_finsetSum Q.support (fun k hk =>
    (tendsto_cauchySeries_monomial_sub hp k).const_mul (Q.coeff k))
  simpa only [heq, mul_zero, Finset.sum_const_zero] using h

theorem DK_ne_zero_at_lattice (hp : 2 ≤ p) (n m : ℕ) :
    DK p n (((p : ℝ)⁻¹)^(m + 1)) ≠ 0 := by
  unfold DK
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  rw [← pow_add]
  exact ne_of_gt (sub_pos.mpr (inv_base_pow_lt_one hp (by omega)))

theorem hasSum_cauchy_exterior (hp : 2 ≤ p) {a : ℕ} (ha : 1 ≤ a) :
    HasSum (fun m : ℕ => theta (theta (fun x : ℝ => ((p : ℝ)^a - x)⁻¹))
      (((p : ℝ)⁻¹)^(m+1))) (cauchyF p ((p : ℝ)^a)) := by
  have he : (fun x : ℝ => ((p : ℝ)^a - x)⁻¹) =
      (fun x : ℝ => (-1) / (x - (p : ℝ)^a)) := by
    funext x
    rw [← neg_sub x ((p : ℝ)^a), inv_neg]
    simp only [neg_div, one_div]
  have hs : Summable (fun m : ℕ => theta (theta (fun x : ℝ => ((p : ℝ)^a - x)⁻¹))
      (((p : ℝ)⁻¹)^(m+1))) := by
    rw [he]
    exact (hasSum_residuePole hp a ha (-1)).summable
  rw [cauchyF_eq p _ (fun m => (lattice_node_ne_pole hp a m).symm)]
  exact hs.hasSum

/-- Orthogonality forces exact interpolation at each exterior root of the
moving denominator.  All identities are taken near support nodes, so no
division at a polynomial zero is assumed. -/
theorem cauchyPolynomialPart_interpolates (hp : 2 ≤ p) {n : ℕ} (Q : ℝ[X])
    (horth : ∀ j : Fin n, Lfun p (fun x => x ^ j.val * Q.eval x / DK p n x) = 0)
    {a : ℕ} (ha : a ∈ Icc 1 n) :
    cauchyF p ((p : ℝ)^a) * Q.eval ((p : ℝ)^a) -
      (cauchyPolynomialPart p Q).eval ((p : ℝ)^a) = 0 := by
  let z : ℝ := (p : ℝ)^a
  obtain ⟨H, hdegree, hH⟩ := denominator_node_quotient hp ha
  have horth' : ∀ j : Fin n, numeratorFunctional hp n (X ^ j.val * Q) = 0 := by
    simpa [numeratorFunctional] using horth
  have hzero : numeratorFunctional hp n (H * Q) = 0 :=
    orthogonal_to_polynomial (numeratorFunctional hp n) Q H horth' hdegree
  let B : ℝ[X] := realDivDiff Q z
  have hBcont : ∀ m : ℕ, ContDiffAt ℝ 2 B.eval (((p : ℝ)⁻¹)^(m+1)) := by
    intro m
    simpa [DK] using contDiffAt_poly_div_DK hp 0 B m
  have hBsum : HasSum (fun m : ℕ => theta (theta B.eval) (((p : ℝ)⁻¹)^(m+1)))
      (numeratorFunctional hp 0 B) := by
    simpa [DK, numeratorFunctional, Lfun] using (hasSum_poly_div_DK hp 0 B).summable.hasSum
  have hIcont : ∀ m : ℕ, ContDiffAt ℝ 2 (fun x : ℝ => (z - x)⁻¹)
      (((p : ℝ)⁻¹)^(m+1)) := by
    intro m
    exact (contDiffAt_const.sub contDiffAt_id).inv
      (sub_ne_zero.mpr (lattice_node_ne_pole hp a m).symm)
  have hIsum := hasSum_cauchy_exterior hp (Finset.mem_Icc.mp ha).1
  have hsum := hasSum_functional_add
    (fun m => contDiffAt_const.mul (hIcont m))
    (fun m => contDiffAt_const.mul (hBcont m))
    (hasSum_functional_const_mul hIcont hIsum (Q.eval z))
    (hasSum_functional_const_mul hBcont hBsum (-1))
  have hsame : ∀ m : ℕ,
      (fun x => (H * Q).eval x / DK p n x) =ᶠ[𝓝 (((p : ℝ)⁻¹)^(m+1))]
      ((fun x => Q.eval z * (z - x)⁻¹) + (fun x => (-1) * B.eval x)) := by
    intro m
    have hDc : Continuous (DK p n) := by unfold DK; fun_prop
    have heD := hDc.continuousAt.eventually_ne (DK_ne_zero_at_lattice hp n m)
    have hez : ∀ᶠ x in 𝓝 (((p : ℝ)⁻¹)^(m+1)), z - x ≠ 0 :=
      (continuous_const.sub continuous_id).continuousAt.eventually_ne
        (sub_ne_zero.mpr (lattice_node_ne_pole hp a m).symm)
    filter_upwards [heD, hez] with x hxD hxz
    have hHx : H.eval x ≠ 0 := by
      have : (z - x) * H.eval x ≠ 0 := by
        change ((p : ℝ)^a - x) * H.eval x ≠ 0
        rwa [← hH x]
      exact (mul_ne_zero_iff.mp this).2
    have hdiff := realDivDiff_identity Q z x
    simp only [Polynomial.eval_mul, Pi.add_apply]
    rw [hH x]
    change H.eval x * Q.eval x / ((z-x)*H.eval x) = Q.eval z * (z-x)⁻¹ + (-1)*B.eval x
    field_simp
    dsimp [B] at *
    nlinarith
  have heval := (hasSum_functional_congr hsame hsum).tsum_eq
  change numeratorFunctional hp n (H * Q) = _ at heval
  rw [hzero] at heval
  rw [cauchyPolynomialPart_eval hp]
  change cauchyF p z * Q.eval z - numeratorFunctional hp 0 B = 0
  linarith

/-- Every orthogonal numerator has the required Cauchy interpolant. -/
theorem cauchy_orthogonal_interpolant (hp : 2 ≤ p) (n : ℕ) (Q : ℝ[X])
    (horth : ∀ j : Fin n, Lfun p (fun x => x ^ j.val * Q.eval x / DK p n x) = 0) :
    ∃ P : ℝ[X],
      Tendsto (fun x => cauchyF p x * Q.eval x - P.eval x) atTop (𝓝 0) ∧
      ∀ a, a < n → cauchyF p ((p : ℝ) ^ (a + 1)) *
        Q.eval ((p : ℝ) ^ (a + 1)) - P.eval ((p : ℝ) ^ (a + 1)) = 0 := by
  refine ⟨cauchyPolynomialPart p Q, tendsto_cauchyPolynomialPart_error hp Q, ?_⟩
  intro a ha
  apply cauchyPolynomialPart_interpolates hp Q horth
  simp only [Finset.mem_Icc]
  omega

end QZeta3
