import QZeta3.GenericGram
import QZeta3.LowClusterEntries
import QZeta3.ClusterCounts
import QZeta3.PolynomialMomentRank

/-! From local cluster entries to the original determinant. -/
open Polynomial Finset Matrix
namespace QZeta3.Generic

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

noncomputable def unnormalizedGram (z : 𝕜) (K : ℕ) (G : Fin K → 𝕜[X]) :
    Matrix (Fin K) (Fin K) 𝕜[X] :=
  Matrix.of fun i j => momentPolynomial z K (G i * G j)

omit [CharZero 𝕜] in
theorem C_mem_lifts_regularAt (ω : 𝕜) (x : RatFunc 𝕜) (hx : x∈regularAt ω) :
    C x ∈ Polynomial.liftsRing (regularAt ω).subtype :=
  (Polynomial.lifts_iff_liftsRing _ _).mp (Polynomial.C'_mem_lifts ⟨⟨x,hx⟩,rfl⟩)

omit [CharZero 𝕜] in
/-- Regularity of a scaled Gram determinant descends through the local basis change. -/
theorem Delta_scaled_coeff_mem_of_gram (ω : 𝕜) (_hω0 : ω≠0) (K E : ℕ)
    (G : Fin K → (RatFunc 𝕜)[X]) (hG : ∀ i, (G i).natDegree<K)
    (hU0 : (polynomialChange K G).det≠0)
    (hUinv : (polynomialChange K G).det⁻¹∈regularAt ω)
    (hdet : C (uniformizer ω)^E * (unnormalizedGram RatFunc.X K G).det ∈
      Polynomial.liftsRing (regularAt ω).subtype) (i : ℕ) :
    uniformizer ω^E * (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i∈regularAt ω := by
  let T := Polynomial.liftsRing (regularAt ω).subtype
  have hnrm := C_mem_lifts_regularAt ω (nrm (RatFunc.X : RatFunc 𝕜) K)
    (nrm_mem_regularAt ω K)
  have hinv := C_mem_lifts_regularAt ω ((polynomialChange K G).det⁻¹) hUinv
  have hmem := T.mul_mem (T.pow_mem hinv 2) (T.mul_mem (T.pow_mem hnrm K) hdet)
  have hnorm : (normalizedGram (RatFunc.X : RatFunc 𝕜) K G).det =
      C (nrm (RatFunc.X : RatFunc 𝕜) K)^K * (unnormalizedGram RatFunc.X K G).det := by
    have hmatrix : normalizedGram (RatFunc.X : RatFunc 𝕜) K G =
        C (nrm (RatFunc.X : RatFunc 𝕜) K) • unnormalizedGram RatFunc.X K G := by
      ext a b
      rfl
    rw [hmatrix, Matrix.det_smul, Fintype.card_fin]
  have hidentity : C ((polynomialChange K G).det⁻¹)^2 *
      (C (nrm (RatFunc.X : RatFunc 𝕜) K)^K *
        (C (uniformizer ω)^E * (unnormalizedGram RatFunc.X K G).det)) =
      C (uniformizer ω)^E * Delta (RatFunc.X : RatFunc 𝕜) K := by
    calc _ = C (uniformizer ω)^E *
        (C ((polynomialChange K G).det⁻¹)^2 * (normalizedGram RatFunc.X K G).det) := by
          rw [hnorm]
          ring
      _ = _ := by
        rw [det_normalizedGram RatFunc.X K G hG]
        have hc : C ((polynomialChange K G).det⁻¹)^2 * C ((polynomialChange K G).det)^2 =
            (1 : (RatFunc 𝕜)[X]) := by
          rw [← mul_pow, ← map_mul, inv_mul_cancel₀ hU0, map_one, one_pow]
        rw [← mul_assoc (C ((polynomialChange K G).det⁻¹)^2), hc, one_mul]
  rw [hidentity] at hmem
  have hcoeff := (coeff_mem_iff_lifts (regularAt ω) _).mpr hmem i
  simpa only [← map_pow, Polynomial.coeff_C_mul] using hcoeff

omit [CharZero 𝕜] in
/-- A bound for a smaller clearing exponent also clears at every larger exponent. -/
theorem uniformizer_pow_mul_mem_of_le (ω : 𝕜) (x : RatFunc 𝕜) {a b : ℕ}
    (hab : a≤b) (h : uniformizer ω^a*x∈regularAt ω) :
    uniformizer ω^b*x∈regularAt ω := by
  have hm := (regularAt ω).mul_mem ((regularAt ω).pow_mem (uniformizer_mem ω) (b-a)) h
  convert hm using 1
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hab]

/-- The low-range cluster weights clear the full unnormalized Gram determinant. -/
theorem low_gram_det_mem {ω : 𝕜} {K d : ℕ} (hω : IsPrimitiveRoot ω d)
    (hd : 0<d) (hω0 : ω≠0) (e : Fin K ≃ ClusterIndex K d) :
    let G := fun i : Fin K => movingClusterPoly (RatFunc.X : RatFunc 𝕜) (RatFunc.C ω)
      K d (e i).1.val (e i).2.val
    let r := fun i : Fin K => clusterRowWeight (clusterMultiplicity K d (e i).1.val) (e i).2.val
    let c := fun i : Fin K => clusterColWeight (clusterMultiplicity K d (e i).1.val) (e i).2.val
    C (uniformizer ω)^((∑ i, r i)+(∑ i, c i)) * (unnormalizedGram RatFunc.X K G).det∈
      Polynomial.liftsRing (regularAt ω).subtype := by
  intro G r c
  apply QZeta3.det_weighted_mem_subring
  intro i j
  apply (coeff_mem_iff_lifts (regularAt ω) _).mp
  intro l
  simpa only [← map_pow, unnormalizedGram, Matrix.of_apply, momentPolynomial, G, r, c] using
    movingCluster_scaled_entry_formula_mem hω hd hω0 K
      (e i).1.val (e j).1.val (e i).2.val (e j).2.val l

/-- The low-range total degree cost is at most the stated cyclotomic exponent. -/
theorem low_weight_cost_le {K d : ℕ} (hd : 0<d) (hlo : 2*d≤K)
    (e : Fin K ≃ ClusterIndex K d) :
    (∑ i : Fin K, clusterRowWeight (clusterMultiplicity K d (e i).1.val) (e i).2.val) +
      (∑ i : Fin K, clusterColWeight (clusterMultiplicity K d (e i).1.val) (e i).2.val) ≤
        cApp K d := by
  rw [← Finset.sum_add_distrib]
  have he := e.sum_comp (fun i : ClusterIndex K d =>
    clusterRowWeight (clusterMultiplicity K d i.1.val) i.2.val +
      clusterColWeight (clusterMultiplicity K d i.1.val) i.2.val)
  rw [he]
  exact sum_cluster_weights_sigma_le_cApp hd hlo

/-- The determinant of a matrix after independent row and column scalings. -/
theorem det_weighted_eq {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (τ : R) (M : Matrix ι ι R) (r c : ι→ℕ) :
    (Matrix.of fun i j => τ^(r i+c j)*M i j).det =
      τ^((∑ i, r i)+(∑ i, c i))*M.det := by
  have hA : (Matrix.of fun i j => τ^(r i+c j)*M i j) =
      Matrix.of fun i j => τ^(r i)*(Matrix.of fun k l => τ^(c l)*M k l) i j := by
    ext i j
    simp only [Matrix.of_apply, pow_add]
    ring
  rw [hA, Matrix.det_mul_column, Matrix.det_mul_row,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, pow_add]
  ring

/-- In the high range the only remaining polynomial-moment pole has controlled rank. -/
theorem high_gram_det_mem {ω : 𝕜} {K d : ℕ} (hω : IsPrimitiveRoot ω d)
    (hω0 : ω≠0) (hKd : K<2*d) (G : Fin K→(RatFunc 𝕜)[X])
    (hGdegree : ∀ i, (G i).natDegree<K) (hGcoeff : ∀ i j, (G i).coeff j∈regularAt ω)
    (r c : Fin K→ℕ)
    (hproper : ∀ i j, C (uniformizer ω^(r i+c j)) *
      (∑ a ∈ Icc 1 K, C ((G i*G j).eval (RatFunc.X^a) /
        (RatFunc.X^a * (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X^a))) *
        (X-C (S (RatFunc.X : RatFunc 𝕜) a)))∈Polynomial.liftsRing (regularAt ω).subtype) :
    C (uniformizer ω)^((∑ i, r i)+(∑ i, c i)+(K-d-1)) *
      (unnormalizedGram RatFunc.X K G).det∈Polynomial.liftsRing (regularAt ω).subtype := by
  classical
  let T := Polynomial.liftsRing (regularAt ω).subtype
  obtain ⟨A,B,hA,hB,hBrank,hAB⟩ := high_quotient_matrix_split ω hω0 d K hω hKd
    G hGdegree hGcoeff r c
  let P : Matrix (Fin K) (Fin K) (RatFunc 𝕜)[X] := fun i j =>
    C (uniformizer ω^(r i+c j)) *
      (∑ a ∈ Icc 1 K, C ((G i*G j).eval (RatFunc.X^a) /
        (RatFunc.X^a * (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X^a))) *
        (X-C (S (RatFunc.X : RatFunc 𝕜) a)))
  let A' : Matrix (Fin K) (Fin K) (RatFunc 𝕜)[X] := A.map C-P
  have hA' (i j : Fin K) : A' i j∈T :=
    T.sub_mem (C_mem_lifts_regularAt ω _ (hA i j)) (hproper i j)
  have hB' (i j : Fin K) : C (B i j)∈T := C_mem_lifts_regularAt ω _ (hB i j)
  have hmem := QZeta3.C_pow_mul_det_add_inv_mem_subring T (uniformizer ω)
    (uniformizer_ne_zero ω) (C_mem_lifts_regularAt ω _ (uniformizer_mem ω))
    A' B hA' hB' (K-d-1) hBrank
  have heq : A'+C ((uniformizer ω)⁻¹) • B.map C =
      Matrix.of fun i j => C (uniformizer ω)^(r i+c j)*
        unnormalizedGram RatFunc.X K G i j := by
    apply Matrix.ext
    intro i j
    change C (A i j)-P i j+C ((uniformizer ω)⁻¹)*C (B i j)=_
    simp only [P, unnormalizedGram, Matrix.of_apply, momentPolynomial,
      ← map_pow, mul_sub, ← map_mul]
    rw [hAB i j, map_add, map_mul]
    ring
  rw [heq, det_weighted_eq] at hmem
  simpa only [← mul_assoc, ← pow_add, Nat.add_comm (K-d-1)] using hmem

end QZeta3.Generic
