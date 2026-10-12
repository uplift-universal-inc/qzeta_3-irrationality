import QZeta3.GenericMoments
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Eval.SMul

/-! # The generic polynomial moment functional and Gram congruence -/

open Polynomial Finset Matrix

namespace QZeta3.Generic

variable {𝕜 : Type*} [Field 𝕜]

noncomputable def LpolyLinear (z : 𝕜) : 𝕜[X] →ₗ[𝕜] 𝕜 :=
  Polynomial.lsum (fun j => LinearMap.mulRight 𝕜 (mu z j))

@[simp] theorem LpolyLinear_apply (z : 𝕜) (f : 𝕜[X]) :
    LpolyLinear z f = Lpoly z f := rfl

theorem Lpoly_add (z : 𝕜) (f g : 𝕜[X]) : Lpoly z (f+g) = Lpoly z f + Lpoly z g :=
  (LpolyLinear z).map_add f g

theorem Lpoly_smul (z c : 𝕜) (f : 𝕜[X]) : Lpoly z (c • f) = c * Lpoly z f :=
  (LpolyLinear z).map_smul c f

noncomputable def momentPolynomial (z : 𝕜) (K : ℕ) (f : 𝕜[X]) : 𝕜[X] :=
  C (Lpoly z (f /ₘ F z K)) - ∑ a ∈ Icc 1 K,
    C (f.eval (z^a) / (z^a * (derivative (F z K)).eval (z^a))) * (X-C (S z a))

noncomputable def momentFunctional (z : 𝕜) (K : ℕ) : 𝕜[X] →ₗ[𝕜] 𝕜[X] where
  toFun := momentPolynomial z K
  map_add' f g := by
    simp only [momentPolynomial, Polynomial.add_divByMonic, Lpoly_add, map_add,
      Polynomial.eval_add, add_div, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c f := by
    simp only [momentPolynomial, Polynomial.smul_divByMonic, Lpoly_smul,
      Polynomial.eval_smul, smul_eq_mul, mul_div_assoc, map_mul, RingHom.id_apply]
    rw [Polynomial.smul_eq_C_mul, mul_sub, Finset.mul_sum]
    congr 1
    apply sum_congr rfl
    intro a ha
    ring

@[simp] theorem momentFunctional_apply (z : 𝕜) (K : ℕ) (f : 𝕜[X]) :
    momentFunctional z K f = momentPolynomial z K f := rfl

/-- The generalized functional agrees exactly with the original formal moments. -/
theorem momentPolynomial_monomial (z : 𝕜) (K k : ℕ) :
    momentPolynomial z K (X^k) = X*C (mLin z K k) + C (mConst z K k) := by
  have he (a : ℕ) : (X^k : 𝕜[X]).eval (z^a) /
      (z^a * (derivative (F z K)).eval (z^a)) = res z K k a / z^a := by
    simp only [Polynomial.eval_pow, Polynomial.eval_X, res, ← pow_mul]
    ring
  simp only [momentPolynomial, he, mLin, mConst, map_neg, map_add, map_sum]
  rw [mul_neg, Finset.mul_sum]
  have hsum : (∑ a ∈ Icc 1 K, C (res z K k a / z^a) * (X-C (S z a))) =
      (∑ a ∈ Icc 1 K, X*C (res z K k a / z^a)) -
        ∑ a ∈ Icc 1 K, C (res z K k a * S z a / z^a) := by
    rw [← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro a ha
    rw [mul_sub, ← map_mul]
    congr 1
    · ring
    · congr 1
      ring
  rw [hsum]
  ring

noncomputable def normalizedGram (z : 𝕜) (K : ℕ) (G : Fin K → 𝕜[X]) :
    Matrix (Fin K) (Fin K) 𝕜[X] :=
  Matrix.of fun i j => C (nrm z K) * momentPolynomial z K (G i * G j)

noncomputable def polynomialChange (K : ℕ) (G : Fin K → 𝕜[X]) : Matrix (Fin K) (Fin K) 𝕜 :=
  Matrix.of fun i j => (G i).coeff j.val

theorem normalizedGram_congruence (z : 𝕜) (K : ℕ) (G : Fin K → 𝕜[X])
    (hG : ∀ i, (G i).natDegree < K) :
    normalizedGram z K G = (polynomialChange K G).map C *
      ((X : 𝕜[X]) • (hankelLin z K).map C + (hankelConst z K).map C) *
      ((polynomialChange K G).map C).transpose := by
  let U := polynomialChange K G
  let L : 𝕜[X] →ₗ[𝕜] 𝕜[X] := (nrm z K) • momentFunctional z K
  have hexp (i : Fin K) : G i = ∑ j : Fin K, U i j • (X : 𝕜[X])^j.val := by
    have h := (G i).as_sum_range_C_mul_X_pow' (hG i)
    rw [← Fin.sum_univ_eq_sum_range _ K] at h
    simpa only [U, polynomialChange, Matrix.of_apply, Polynomial.smul_eq_C_mul] using h
  have hmono (i j : Fin K) :
      L ((X : 𝕜[X])^(i.val+j.val)) =
        ((X : 𝕜[X]) • (hankelLin z K).map C + (hankelConst z K).map C) i j := by
    simp only [L, LinearMap.smul_apply, momentFunctional_apply, momentPolynomial_monomial,
      Polynomial.smul_eq_C_mul, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
      hankelLin, hankelConst, Matrix.of_apply, smul_eq_mul, map_mul]
    ring
  apply Matrix.ext
  intro i j
  have hid : normalizedGram z K G i j = L (G i * G j) := by
    simp [normalizedGram, L, Polynomial.smul_eq_C_mul]
  rw [hid]
  rw [hexp i, hexp j]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    ← pow_add, map_sum, map_smul, hmono]
  simp only [Polynomial.smul_eq_C_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  apply sum_congr rfl
  intro s hs
  apply sum_congr rfl
  intro r hr
  ring

/-- The determinant changes by the square of the coefficient determinant. -/
theorem det_normalizedGram (z : 𝕜) (K : ℕ) (G : Fin K → 𝕜[X])
    (hG : ∀ i, (G i).natDegree < K) :
    (normalizedGram z K G).det = C ((polynomialChange K G).det)^2 * Delta z K := by
  rw [normalizedGram_congruence z K G hG, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  have hm : ((polynomialChange K G).map C).det = C ((polynomialChange K G).det) :=
    (RingHom.map_det C (polynomialChange K G)).symm
  rw [hm]
  unfold Delta
  ring

end QZeta3.Generic
