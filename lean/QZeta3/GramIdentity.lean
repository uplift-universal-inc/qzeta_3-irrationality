import QZeta3.Functional
import QZeta3.DividedDifferences

open Polynomial Finset Filter Topology

namespace QZeta3

/-- The moving real denominator. -/
noncomputable def DK (p K : ℕ) (x : ℝ) : ℝ :=
  ∏ a ∈ Icc 1 K, (1 - ((p : ℝ)⁻¹)^a * x)

/-- The real matrix of the functional on monomials over the moving denominator. -/
noncomputable def gramR (p K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  Matrix.of fun i j => Lfun p (fun x => x^(i.val + j.val) / DK p K x)

theorem lattice_node_ne_pole {p : ℕ} (hp : 2 ≤ p) (a m : ℕ) :
    ((p : ℝ)⁻¹)^(m + 1) ≠ (p : ℝ)^a := by
  have h₁ := inv_base_pow_lt_one hp (show 0 < m + 1 by omega)
  have h₂ : 1 ≤ (p : ℝ)^a := one_le_pow₀ (by exact_mod_cast (show 1 ≤ p by omega))
  exact ne_of_lt (lt_of_lt_of_le h₁ h₂)

theorem reciprocal_pole_eq {p : ℕ} (hp : 2 ≤ p) (a : ℕ) :
    (fun x : ℝ => (x - (p : ℝ)^a)⁻¹) =
      (fun x => -((p : ℝ)^a)⁻¹ * (1 - ((p : ℝ)⁻¹)^a * x)⁻¹) := by
  funext x
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have he : x - (p : ℝ)^a = -(p : ℝ)^a * (1 - ((p : ℝ)⁻¹)^a * x) := by
    rw [inv_pow]
    field_simp
    ring
  rw [he, mul_inv, inv_neg]

theorem contDiffAt_residuePole {p : ℕ} (hp : 2 ≤ p) (a : ℕ) (c : ℝ) (m : ℕ) :
    ContDiffAt ℝ 2 (fun x => c / (x - (p : ℝ)^a)) (((p : ℝ)⁻¹)^(m + 1)) := by
  exact contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const)
    (sub_ne_zero.mpr (lattice_node_ne_pole hp a m))

theorem hasSum_residuePole {p : ℕ} (hp : 2 ≤ p) (a : ℕ) (ha : 1 ≤ a) (c : ℝ) :
    HasSum (fun m : ℕ => theta (theta (fun x => c / (x - (p : ℝ)^a)))
      (((p : ℝ)⁻¹)^(m + 1))) ((-c / (p : ℝ)^a) * (xi p - (S p a : ℝ))) := by
  have he : (fun x : ℝ => c / (x - (p : ℝ)^a)) =
      (fun x => (-c / (p : ℝ)^a) * (1 - ((p : ℝ)⁻¹)^a * x)⁻¹) := by
    funext x
    simp only [div_eq_mul_inv]
    rw [congrFun (reciprocal_pole_eq hp a) x]
    ring
  rw [he]
  exact hasSum_functional_const_mul (contDiffAt_simplePole hp)
    (hasSum_simplePole hp a ha) (-c / (p : ℝ)^a)

theorem contDiffAt_fraction_F {p : ℕ} (hp : 2 ≤ p) (K k m : ℕ) :
    ContDiffAt ℝ 2 (fun x : ℝ => x^k / (F p K).eval₂ (Rat.castHom ℝ) x)
      (((p : ℝ)⁻¹)^(m + 1)) := by
  have hn : (F p K).eval₂ (Rat.castHom ℝ) (((p : ℝ)⁻¹)^(m + 1)) ≠ 0 := by
    simp only [F, Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C, Rat.coe_castHom, Rat.cast_pow, Rat.cast_natCast]
    exact Finset.prod_ne_zero_iff.mpr (fun a ha => sub_ne_zero.mpr (lattice_node_ne_pole hp a m))
  exact (contDiffAt_id.pow k).div (contDiffAt_ratPolynomial (F p K) _) hn

/-- Analytic convergence and exact value of every monomial moment over `F_K`. -/
theorem hasSum_fraction_F {p : ℕ} (hp : 2 ≤ p) (K k : ℕ) :
    HasSum (fun m : ℕ => theta (theta (fun x : ℝ =>
      x^k / (F p K).eval₂ (Rat.castHom ℝ) x)) (((p : ℝ)⁻¹)^(m + 1)))
      ((mConst p K k : ℝ) + (mLin p K k : ℝ) * xi p) := by
  let U := X^k /ₘ F p K
  let R : ℕ → ℝ → ℝ := fun a x => (res p K k a : ℝ) / (x - (p : ℝ)^a)
  have hs := hasSum_functional_sum (Icc 1 K) R
    (fun a => (-(res p K k a : ℝ) / (p : ℝ)^a) * (xi p - (S p a : ℝ)))
    (fun a _ m => contDiffAt_residuePole hp a _ m)
    (fun a ha => hasSum_residuePole hp a (mem_Icc.mp ha).1 _)
  have hsum := hasSum_functional_add
    (fun m => contDiffAt_ratPolynomial U _)
    (fun m => ContDiffAt.sum (fun a _ => contDiffAt_residuePole hp a _ m))
    (hasSum_polynomial hp U) hs
  have he : ∀ m : ℕ, (fun x : ℝ => x^k / (F p K).eval₂ (Rat.castHom ℝ) x) =ᶠ[
      𝓝 (((p : ℝ)⁻¹)^(m + 1))]
      ((fun x => U.eval₂ (Rat.castHom ℝ) x) + (fun x => ∑ a ∈ Icc 1 K, R a x)) := by
    intro m
    filter_upwards [Iio_mem_nhds (inv_base_pow_lt_one hp (show 0 < m + 1 by omega))] with x hx
    apply partial_fraction_real hp K k x
    intro a ha
    exact ne_of_lt (lt_of_lt_of_le hx
      (one_le_pow₀ (by exact_mod_cast (show 1 ≤ p by omega))))
  convert hasSum_functional_congr he hsum using 1
  simp only [mConst, mLin, Rat.cast_add, Rat.cast_sum, Rat.cast_div, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_neg, U]
  rw [neg_mul, Finset.sum_mul]
  rw [add_assoc, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro a ha
  ring

theorem fraction_DK_eq {p : ℕ} (hp : 2 ≤ p) (K k : ℕ) :
    (fun x : ℝ => x^k / DK p K x) =
      (fun x => (nrm p K : ℝ) * (x^k / (F p K).eval₂ (Rat.castHom ℝ) x)) := by
  funext x
  rw [DK, denominator_normalization hp]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- All entries of the moving-denominator matrix are convergent affine moments. -/
theorem hasSum_fraction_DK {p : ℕ} (hp : 2 ≤ p) (K k : ℕ) :
    HasSum (fun m : ℕ => theta (theta (fun x : ℝ => x^k / DK p K x))
      (((p : ℝ)⁻¹)^(m + 1)))
      ((nrm p K : ℝ) * ((mConst p K k : ℝ) + (mLin p K k : ℝ) * xi p)) := by
  rw [fraction_DK_eq hp]
  exact hasSum_functional_const_mul (contDiffAt_fraction_F hp K k)
    (hasSum_fraction_F hp K k) (nrm p K : ℝ)

theorem Lfun_fraction_DK {p : ℕ} (hp : 2 ≤ p) (K k : ℕ) :
    Lfun p (fun x : ℝ => x^k / DK p K x) =
      (nrm p K : ℝ) * ((mConst p K k : ℝ) + (mLin p K k : ℝ) * xi p) :=
  (hasSum_fraction_DK hp K k).tsum_eq

theorem contDiffAt_fraction_DK {p : ℕ} (hp : 2 ≤ p) (K k m : ℕ) :
    ContDiffAt ℝ 2 (fun x : ℝ => x^k / DK p K x) (((p : ℝ)⁻¹)^(m + 1)) := by
  rw [fraction_DK_eq hp]
  exact contDiffAt_const.mul (contDiffAt_fraction_F hp K k m)

/-- A real polynomial divided by `D_K` is a finite real linear combination of its monomials. -/
theorem poly_div_DK_eq_sum (p K : ℕ) (P : ℝ[X]) :
    (fun x : ℝ => P.eval x / DK p K x) =
      (fun x => ∑ j ∈ P.support, P.coeff j * (x^j / DK p K x)) := by
  funext x
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_div]
  apply sum_congr rfl
  intro j hj
  ring

theorem contDiffAt_poly_div_DK {p : ℕ} (hp : 2 ≤ p) (K : ℕ) (P : ℝ[X]) (m : ℕ) :
    ContDiffAt ℝ 2 (fun x : ℝ => P.eval x / DK p K x) (((p : ℝ)⁻¹)^(m + 1)) := by
  rw [poly_div_DK_eq_sum]
  exact ContDiffAt.sum (fun j _ => contDiffAt_const.mul (contDiffAt_fraction_DK hp K j m))

/-- Every real polynomial numerator defines a convergent moment series. -/
theorem hasSum_poly_div_DK {p : ℕ} (hp : 2 ≤ p) (K : ℕ) (P : ℝ[X]) :
    HasSum (fun m : ℕ => theta (theta (fun x : ℝ => P.eval x / DK p K x))
      (((p : ℝ)⁻¹)^(m + 1)))
      (∑ j ∈ P.support, P.coeff j *
        ((nrm p K : ℝ) * ((mConst p K j : ℝ) + (mLin p K j : ℝ) * xi p))) := by
  rw [poly_div_DK_eq_sum]
  exact hasSum_functional_sum P.support
    (fun j x => P.coeff j * (x^j / DK p K x)) _
    (fun j _ m => contDiffAt_const.mul (contDiffAt_fraction_DK hp K j m))
    (fun j _ => hasSum_functional_const_mul (contDiffAt_fraction_DK hp K j)
      (hasSum_fraction_DK hp K j) (P.coeff j))

theorem Lfun_poly_div_DK_add {p : ℕ} (hp : 2 ≤ p) (K : ℕ) (P Q : ℝ[X]) :
    Lfun p (fun x => (P + Q).eval x / DK p K x) =
      Lfun p (fun x => P.eval x / DK p K x) + Lfun p (fun x => Q.eval x / DK p K x) := by
  have hs := hasSum_functional_add
    (contDiffAt_poly_div_DK hp K P) (contDiffAt_poly_div_DK hp K Q)
    (hasSum_poly_div_DK hp K P).summable.hasSum (hasSum_poly_div_DK hp K Q).summable.hasSum
  have he : (fun x => (P + Q).eval x / DK p K x) =
      (fun x => P.eval x / DK p K x) + (fun x => Q.eval x / DK p K x) := by
    funext x
    simp only [Polynomial.eval_add, Pi.add_apply, add_div]
  rw [he]
  exact hs.tsum_eq

theorem Lfun_poly_div_DK_smul {p : ℕ} (hp : 2 ≤ p) (K : ℕ) (P : ℝ[X]) (c : ℝ) :
    Lfun p (fun x => (c • P).eval x / DK p K x) = c * Lfun p (fun x => P.eval x / DK p K x) := by
  have hs := hasSum_functional_const_mul (contDiffAt_poly_div_DK hp K P)
    (hasSum_poly_div_DK hp K P).summable.hasSum c
  have he : (fun x => (c • P).eval x / DK p K x) =
      (fun x => c * (P.eval x / DK p K x)) := by
    funext x
    simp only [Polynomial.eval_smul, smul_eq_mul]
    ring
  rw [he]
  exact hs.tsum_eq

/-- The functional on real polynomial numerators over the fixed moving denominator. -/
noncomputable def numeratorFunctional {p : ℕ} (hp : 2 ≤ p) (K : ℕ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun P := Lfun p (fun x => P.eval x / DK p K x)
  map_add' := Lfun_poly_div_DK_add hp K
  map_smul' c P := by simpa only [smul_eq_mul, RingHom.id_apply] using Lfun_poly_div_DK_smul hp K P c

/-- Evaluation of the formal determinant gives the actual real Gram determinant. -/
theorem gram_det_eq {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    (gramR p K).det = DeltaR p K (xi p) := by
  unfold DeltaR Delta
  change (gramR p K).det = (aeval (xi p)).toRingHom _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [gramR, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, aeval_C,
    hankelLin, hankelConst, Matrix.of_apply]
  rw [Lfun_fraction_DK hp]
  have hcast (r : ℚ) : algebraMap ℚ ℝ r = (r : ℝ) := rfl
  simp only [hcast]
  ring

end QZeta3
