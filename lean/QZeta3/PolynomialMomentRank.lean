import QZeta3.GenericMoments
import QZeta3.CyclotomicLocal
import Mathlib.LinearAlgebra.Matrix.Rank

open Polynomial Finset Matrix

namespace QZeta3.Generic

variable {𝕜 : Type*} [Field 𝕜]

/-- Below degree `2d`, the only nonconstant moment with a possible pole at a primitive
`d`th root is `μ_d`. Subtracting it leaves a regular element. -/
theorem Lpoly_sub_coeff_mu_mem (ω : 𝕜) (d : ℕ) (hω : IsPrimitiveRoot ω d)
    (f : (RatFunc 𝕜)[X]) (hf : ∀ i, f.coeff i ∈ regularAt ω)
    (hdegree : f.natDegree < 2*d) :
    Lpoly RatFunc.X f - f.coeff d * mu RatFunc.X d ∈ regularAt ω := by
  classical
  have heq : Lpoly RatFunc.X f - f.coeff d * mu RatFunc.X d =
      ∑ j ∈ f.support.erase d, f.coeff j * mu RatFunc.X j := by
    unfold Lpoly
    by_cases hd : d ∈ f.support
    · rw [← Finset.sum_erase_add f.support (fun j => f.coeff j * mu RatFunc.X j) hd]
      ring
    · have hc : f.coeff d = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hd
      rw [Finset.erase_eq_of_notMem hd, hc]
      simp
  rw [heq]
  apply (regularAt ω).sum_mem
  intro j hj
  apply (regularAt ω).mul_mem (hf j)
  by_cases hj0 : j = 0
  · simp [mu, hj0]
  · apply mu_mem_regularAt_of_pow_ne_one
    intro hpw
    have hdiv : d ∣ j := (hω.pow_eq_one_iff_dvd j).mp hpw
    have hjd : j ≠ d := (Finset.mem_erase.mp hj).1
    have hjlt : j < 2*d := lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp j
      (Finset.mem_erase.mp hj).2) hdegree
    obtain ⟨k, hk⟩ := hdiv
    have hdpos : 0 < d := by omega
    have hkpos : 0 < k := by
      by_contra h
      have hkzero : k = 0 := by omega
      apply hj0
      simpa [hkzero] using hk
    have hklt : k < 2 := by nlinarith
    have hkone : k = 1 := by omega
    exact hjd (by simpa [hkone] using hk)

noncomputable def quotientMomentMatrix (F : 𝕜[X]) (K d : ℕ) : Matrix (Fin K) (Fin K) 𝕜 :=
  fun i j => (((X : 𝕜[X])^(i.val + j.val)) /ₘ F).coeff d

/-- Low-degree monomials lie in the radical of the coefficient form. -/
theorem quotient_moment_monomial_zero {F : 𝕜[X]} (hF : F.Monic) {K d i j : ℕ}
    (hdegree : F.natDegree = K) (hi : i ≤ d) (hj : j < K) :
    (((X : 𝕜[X])^(i + j)) /ₘ F).coeff d = 0 := by
  by_cases hij : i + j < K
  · have hz : ((X : 𝕜[X])^(i + j)) /ₘ F = 0 := by
      apply (divByMonic_eq_zero_iff hF).mpr
      rw [degree_X_pow, degree_eq_natDegree hF.ne_zero, hdegree]
      exact_mod_cast hij
    simp [hz]
  · apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_divByMonic _ hF, natDegree_X_pow, hdegree]
    omega

theorem rank_quotientMomentMatrix_le {F : 𝕜[X]} (hF : F.Monic) {K : ℕ}
    (hdegree : F.natDegree = K) (d : ℕ) :
    (quotientMomentMatrix F K d).rank ≤ K - d - 1 := by
  classical
  by_cases hd : d < K
  · let a : Fin K := ⟨d, hd⟩
    have h := Matrix.rank_le_card_of_support_subset (quotientMomentMatrix F K d) (Ioi a) (by
      rw [Function.support_subset_iff']
      intro i hi
      ext j
      apply quotient_moment_monomial_zero hF hdegree _ j.isLt
      have hin : ¬a < i := by simpa only [mem_coe, mem_Ioi] using hi
      exact le_of_not_gt hin)
    rw [Fin.card_Ioi] at h
    dsimp [a] at h
    omega
  · have hz : quotientMomentMatrix F K d = 0 := by
      ext i j
      exact quotient_moment_monomial_zero hF hdegree (by omega) j.isLt
    rw [hz, Matrix.rank_zero]
    omega

/-- In any polynomial basis of degree below `K`, the singular `d`th quotient moment
has rank at most `max (0, K-d-1)` (natural subtraction). -/
theorem rank_quotient_moment_le {F : 𝕜[X]} (hF : F.Monic) {K : ℕ}
    (hdegree : F.natDegree = K) (G : Fin K → 𝕜[X])
    (hG : ∀ i, (G i).natDegree < K) (d : ℕ) :
    (Matrix.of fun i j => ((G i * G j) /ₘ F).coeff d).rank ≤ K - d - 1 := by
  classical
  let U : Matrix (Fin K) (Fin K) 𝕜 := fun i j => (G i).coeff j.val
  let L : 𝕜[X] →ₗ[𝕜] 𝕜 := (Polynomial.lcoeff 𝕜 d).comp (Polynomial.divByMonicHom F)
  have hexp (i : Fin K) : G i = ∑ j : Fin K, U i j • (X : 𝕜[X])^j.val := by
    have h := (G i).as_sum_range_C_mul_X_pow' (hG i)
    rw [← Fin.sum_univ_eq_sum_range _ K] at h
    simpa only [U, Polynomial.smul_eq_C_mul] using h
  have hmono (i j : Fin K) : L ((X : 𝕜[X])^(i.val + j.val)) = quotientMomentMatrix F K d i j := rfl
  have heq : (Matrix.of fun i j => ((G i * G j) /ₘ F).coeff d) =
      U * quotientMomentMatrix F K d * U.transpose := by
    ext i j
    change L (G i * G j) = _
    rw [hexp i, hexp j]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      ← pow_add, map_sum, map_smul, smul_eq_mul, hmono]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    apply sum_congr rfl
    intro s hs
    apply sum_congr rfl
    intro r hr
    ring
  rw [heq]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_mul_le_right _ _).trans (rank_quotientMomentMatrix_le hF hdegree d))

/-- High-range polynomial moments consist of a regular matrix and one simple-pole
correction of controlled rank, even after arbitrary nonnegative row and column scalings. -/
theorem high_quotient_matrix_split [CharZero 𝕜]
    (ω : 𝕜) (hω0 : ω ≠ 0) (d K : ℕ) (hω : IsPrimitiveRoot ω d) (hKd : K < 2*d)
    (G : Fin K → (RatFunc 𝕜)[X]) (hGdegree : ∀ i, (G i).natDegree < K)
    (hGcoeff : ∀ i j, (G i).coeff j ∈ regularAt ω) (r c : Fin K → ℕ) :
    ∃ A B : Matrix (Fin K) (Fin K) (RatFunc 𝕜),
      (∀ i j, A i j ∈ regularAt ω) ∧ (∀ i j, B i j ∈ regularAt ω) ∧
      B.rank ≤ K - d - 1 ∧
      ∀ i j, uniformizer ω^(r i+c j) * Lpoly RatFunc.X ((G i*G j) /ₘ F RatFunc.X K) =
        A i j + (uniformizer ω)⁻¹ * B i j := by
  classical
  let H : Fin K → Fin K → (RatFunc 𝕜)[X] := fun i j => (G i*G j) /ₘ F RatFunc.X K
  let M : Matrix (Fin K) (Fin K) (RatFunc 𝕜) := fun i j => (H i j).coeff d
  let A : Matrix (Fin K) (Fin K) (RatFunc 𝕜) := fun i j =>
    uniformizer ω^(r i+c j) * (Lpoly RatFunc.X (H i j) - (H i j).coeff d * mu RatFunc.X d)
  let B : Matrix (Fin K) (Fin K) (RatFunc 𝕜) := fun i j =>
    uniformizer ω^(r i+c j) * (uniformizer ω * mu RatFunc.X d) * (H i j).coeff d
  have hHcoeff (i j : Fin K) (l : ℕ) : (H i j).coeff l ∈ regularAt ω := by
    apply quotient_coeff_mem_subring (regularAt ω) RatFunc.X (base_mem_regularAt ω) K
    apply (coeff_mem_iff_lifts (regularAt ω) (G i*G j)).mpr
    exact (Polynomial.liftsRing (regularAt ω).subtype).mul_mem
      ((coeff_mem_iff_lifts _ _).mp (hGcoeff i)) ((coeff_mem_iff_lifts _ _).mp (hGcoeff j))
  have hHdegree (i j : Fin K) : (H i j).natDegree < 2*d := by
    dsimp [H]
    rw [natDegree_divByMonic _ (F_monic _ K), F_natDegree]
    have hprod : (G i*G j).natDegree ≤ (G i).natDegree + (G j).natDegree :=
      Polynomial.natDegree_mul_le
    have hi := hGdegree i
    have hj := hGdegree j
    omega
  have hA (i j : Fin K) : A i j ∈ regularAt ω :=
    (regularAt ω).mul_mem ((regularAt ω).pow_mem (uniformizer_mem ω) _)
      (Lpoly_sub_coeff_mu_mem ω d hω (H i j) (hHcoeff i j) (hHdegree i j))
  have hB (i j : Fin K) : B i j ∈ regularAt ω :=
    (regularAt ω).mul_mem
      ((regularAt ω).mul_mem ((regularAt ω).pow_mem (uniformizer_mem ω) _)
        (uniformizer_mul_mu_mem ω hω0 d)) (hHcoeff i j d)
  have hMrank : M.rank ≤ K-d-1 :=
    rank_quotient_moment_le (F_monic _ K) (F_natDegree _ K) G hGdegree d
  have hBrank : B.rank ≤ K-d-1 := by
    have heq : B = Matrix.diagonal (fun i => uniformizer ω^(r i) * (uniformizer ω*mu RatFunc.X d)) *
        M * Matrix.diagonal (fun j => uniformizer ω^(c j)) := by
      ext i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      dsimp [B, M]
      rw [pow_add]
      ring
    rw [heq]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hMrank)
  refine ⟨A, B, hA, hB, hBrank, ?_⟩
  intro i j
  dsimp [A, B, H]
  have ht : uniformizer ω ≠ 0 := uniformizer_ne_zero ω
  field_simp
  ring

end QZeta3.Generic
