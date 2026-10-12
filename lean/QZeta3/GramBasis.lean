import QZeta3.GramIdentity
import QZeta3.AnalyticDeterminant

open Polynomial Finset Matrix

namespace QZeta3

noncomputable def tripleRootGram (p K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  fun i j => Lfun p (fun x =>
    (tripleRootPoly ((p : ℝ)⁻¹) i.val).eval x *
      (tripleRootPoly ((p : ℝ)⁻¹) j.val).eval x / DK p K x)

theorem tripleRootPoly_expansion (q : ℝ) {K : ℕ} (i : Fin K) :
    tripleRootPoly q i.val = ∑ j : Fin K, (tripleRootChange q K i j) • (X : ℝ[X])^j.val := by
  have h := (tripleRootPoly q i.val).as_sum_range_C_mul_X_pow'
    (show (tripleRootPoly q i.val).natDegree < K by rw [tripleRootPoly_natDegree]; exact i.isLt)
  rw [← Fin.sum_univ_eq_sum_range _ K] at h
  simpa only [tripleRootChange, Polynomial.smul_eq_C_mul] using h

theorem tripleRootGram_eq_congruence {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    tripleRootGram p K = tripleRootChange ((p : ℝ)⁻¹) K * gramR p K *
      (tripleRootChange ((p : ℝ)⁻¹) K).transpose := by
  let L := numeratorFunctional hp K
  have hmono (i j : Fin K) : L ((X : ℝ[X])^(i.val + j.val)) = gramR p K i j := by
    simp only [L, numeratorFunctional, LinearMap.coe_mk, AddHom.coe_mk, gramR,
      Matrix.of_apply, Polynomial.eval_pow, Polynomial.eval_X]
  ext i j
  have hid : tripleRootGram p K i j =
      L (tripleRootPoly ((p : ℝ)⁻¹) i.val * tripleRootPoly ((p : ℝ)⁻¹) j.val) := by
    simp only [tripleRootGram, L, numeratorFunctional, LinearMap.coe_mk, AddHom.coe_mk,
      Polynomial.eval_mul]
  rw [hid]
  rw [tripleRootPoly_expansion _ i, tripleRootPoly_expansion _ j]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    ← pow_add, map_sum, map_smul, smul_eq_mul, hmono]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply sum_congr rfl
  intro s hs
  apply sum_congr rfl
  intro r hr
  ring

/-- The triple-root basis change preserves the actual Gram determinant. -/
theorem det_tripleRootGram {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    (tripleRootGram p K).det = (gramR p K).det := by
  rw [tripleRootGram_eq_congruence hp]
  exact det_congruence_of_det_one _ _ (det_tripleRootChange _ _)

/-- Convergence of every entry in the transformed basis. -/
theorem summable_tripleRootGram_entry {p : ℕ} (hp : 2 ≤ p) (K i j : ℕ) :
    Summable (fun m : ℕ => theta (theta (fun x =>
      (tripleRootPoly ((p : ℝ)⁻¹) i).eval x *
        (tripleRootPoly ((p : ℝ)⁻¹) j).eval x / DK p K x))
      (((p : ℝ)⁻¹)^(m + 1))) := by
  simpa only [Polynomial.eval_mul] using (hasSum_poly_div_DK hp K
    (tripleRootPoly ((p : ℝ)⁻¹) i * tripleRootPoly ((p : ℝ)⁻¹) j)).summable

end QZeta3
