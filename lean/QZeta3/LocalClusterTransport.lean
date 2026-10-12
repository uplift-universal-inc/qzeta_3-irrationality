import QZeta3.ClusterCounts
import QZeta3.GenericGram

/-! Reindexing the local cluster basis onto the original Hankel matrix indices. -/
open Polynomial Finset
namespace QZeta3.Generic

variable {k : Type*} [Field k]

theorem clusterIndex_card (K d : ℕ) (hd : 0<d) :
    Fintype.card (ClusterIndex K d) = K := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact sum_clusterMultiplicity_fin hd

noncomputable def clusterEquivFin (K d : ℕ) (hd : 0<d) : ClusterIndex K d ≃ Fin K :=
  (Fintype.equivFin (ClusterIndex K d)).trans (finCongr (clusterIndex_card K d hd))

noncomputable def transportClusterPoly (ω : k) (K d : ℕ) (hd : 0<d)
    (β : Fin d → regularAt ω) (i : Fin K) : (RatFunc k)[X] :=
  (localClusterPoly ω K d β ((clusterEquivFin K d hd).symm i)).map (regularAt ω).subtype

theorem localClusterPoly_subtype (ω : k) (K d : ℕ) (β : Fin d → regularAt ω)
    (i : ClusterIndex K d) :
    (localClusterPoly ω K d β i).map (regularAt ω).subtype =
      movingClusterComplement (RatFunc.X : RatFunc k) K d i.1.val *
        (X - C (β i.1 : RatFunc k)) ^ i.2.val := by
  simp [localClusterPoly, movingClusterComplement, localBase, Polynomial.map_prod]

theorem transportClusterPoly_eq (ω : k) (K d : ℕ) (hd : 0<d)
    (β : Fin d → regularAt ω) (i : Fin K) :
    transportClusterPoly ω K d hd β i =
      movingClusterComplement (RatFunc.X : RatFunc k) K d
        ((clusterEquivFin K d hd).symm i).1.val *
      (X-C (β ((clusterEquivFin K d hd).symm i).1 : RatFunc k)) ^
        ((clusterEquivFin K d hd).symm i).2.val :=
  localClusterPoly_subtype ω K d β _

theorem transportClusterPoly_coeff_mem (ω : k) (K d : ℕ) (hd : 0<d)
    (β : Fin d → regularAt ω) (i : Fin K) (j : ℕ) :
    (transportClusterPoly ω K d hd β i).coeff j ∈ regularAt ω := by
  unfold transportClusterPoly
  rw [Polynomial.coeff_map]
  exact ((localClusterPoly ω K d β ((clusterEquivFin K d hd).symm i)).coeff j).property

theorem movingClusterComplement_natDegree (z : k) (K d r : ℕ) :
    (movingClusterComplement z K d r).natDegree = K-clusterMultiplicity K d r := by
  rw [movingClusterComplement, Polynomial.natDegree_prod_of_monic _ _
    (fun a _ => monic_X_sub_C _)]
  simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]
  have hc := Finset.card_filter_add_card_filter_not (s := Icc 1 K) (fun a => a%d=r)
  have hc' : clusterMultiplicity K d r + ((Icc 1 K).filter (fun a => a%d≠r)).card = K := by
    simpa only [clusterMultiplicity, clusterIndices, Nat.card_Icc, Nat.add_sub_cancel] using hc
  omega

theorem transportClusterPoly_degree_lt (ω : k) (K d : ℕ) (hd : 0<d)
    (β : Fin d → regularAt ω) (i : Fin K) :
    (transportClusterPoly ω K d hd β i).natDegree < K := by
  rw [transportClusterPoly_eq]
  rw [Polynomial.natDegree_mul (movingClusterComplement_monic _ _ _ _).ne_zero
      (((monic_X_sub_C _).pow _).ne_zero), movingClusterComplement_natDegree,
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have hj := ((clusterEquivFin K d hd).symm i).2.isLt
  have hm : clusterMultiplicity K d ((clusterEquivFin K d hd).symm i).1.val ≤ K := by
    have := Finset.card_filter_le (s := Icc 1 K)
      (p := fun a => a%d=((clusterEquivFin K d hd).symm i).1.val)
    simpa [clusterMultiplicity, clusterIndices] using this
  omega

/-- Reindexing changes neither the local determinant nor its image in the fraction field. -/
theorem transportCluster_det_eq (ω : k) (K d : ℕ) (hd : 0<d)
    (β : Fin d → regularAt ω) :
    (polynomialChange K (transportClusterPoly ω K d hd β)).det =
      ((localClusterMatrix ω K d β).det : RatFunc k) := by
  let e := finCongr (clusterIndex_card K d hd)
  have he : polynomialChange K (transportClusterPoly ω K d hd β) =
      ((localClusterMatrix ω K d β).reindex e e).map (regularAt ω).subtype := by
    ext i j
    simp [polynomialChange, transportClusterPoly, localClusterMatrix,
      clusterEquivFin, Matrix.reindex, Matrix.submatrix, e]
  have hmap := (RingHom.map_det (regularAt ω).subtype
    ((localClusterMatrix ω K d β).reindex e e)).symm
  change (((localClusterMatrix ω K d β).reindex e e).map (regularAt ω).subtype).det =
    (((localClusterMatrix ω K d β).reindex e e).det : RatFunc k) at hmap
  rw [he, hmap, Matrix.det_reindex_self]

theorem transportCluster_det_ne_zero {ω : k} {K d : ℕ} (hω : IsPrimitiveRoot ω d)
    (hd : 0<d) (hdK : d≤K) (β : Fin d → regularAt ω)
    (hβ : ∀ r, localEval ω (β r)=ω^r.val) :
    (polynomialChange K (transportClusterPoly ω K d hd β)).det ≠ 0 := by
  rw [transportCluster_det_eq]
  exact (IsUnit.map (regularAt ω).subtype
    (localClusterMatrix_det_isUnit hω hd hdK β hβ)).ne_zero

theorem transportCluster_det_inv_mem {ω : k} {K d : ℕ} (hω : IsPrimitiveRoot ω d)
    (hd : 0<d) (hdK : d≤K) (β : Fin d → regularAt ω)
    (hβ : ∀ r, localEval ω (β r)=ω^r.val) :
    ((polynomialChange K (transportClusterPoly ω K d hd β)).det)⁻¹ ∈ regularAt ω := by
  rw [transportCluster_det_eq]
  apply inv_mem_regularAt_of_eval_ne_zero
  exact (IsUnit.map (localEval ω) (localClusterMatrix_det_isUnit hω hd hdK β hβ)).ne_zero

end QZeta3.Generic
