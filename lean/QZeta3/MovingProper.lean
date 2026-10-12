import QZeta3.MovingClusterBasis

/-! # Local bounds for the actual moving-cluster proper entries -/

open Polynomial Finset

namespace QZeta3.Generic

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- A cluster basis polynomial vanishes at every node outside its cluster. -/
theorem movingClusterPoly_eval_zero (z η : 𝕜) (K d r j a : ℕ)
    (ha : a ∈ Icc 1 K) (har : a%d ≠ r) :
    (movingClusterPoly z η K d r j).eval (z^a) = 0 := by
  unfold movingClusterPoly
  rw [Polynomial.eval_mul]
  have hcomp : (movingClusterComplement z K d r).eval (z^a) = 0 := by
    unfold movingClusterComplement
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨ha,har⟩)
    simp
  rw [hcomp, zero_mul]

/-- Evaluation of a cluster basis polynomial contains its assigned zero power. -/
theorem movingClusterPoly_eval_div_mem {ω : 𝕜} {d : ℕ} (hω : IsPrimitiveRoot ω d)
    (K r j a : ℕ) (har : a%d = r) :
    (movingClusterPoly (RatFunc.X : RatFunc 𝕜) (RatFunc.C ω) K d r j).eval (RatFunc.X^a) /
      uniformizer ω ^ j ∈ regularAt ω := by
  have hpow : ω^a = ω^r := by rw [pow_eq_pow_mod a hω.pow_eq_one, har]
  have hV := movingClusterComplement_coeff_mem (regularAt ω) RatFunc.X
    (base_mem_regularAt ω) K d r
  have h := cluster_numerator_eval_div_mem ω (ω^r) a j hpow
    (movingClusterComplement RatFunc.X K d r) hV
  simpa only [movingClusterPoly, map_pow] using h

/-- Low-range integer row/column weights clear each individual proper residue
entry in the actual cluster basis. Entries from distinct clusters vanish. -/
theorem movingCluster_proper_term_mem {ω : 𝕜} {d : ℕ} (hω : IsPrimitiveRoot ω d)
    (hd : 0<d) (hω0 : ω≠0) (K r s j k a : ℕ) (ha : a∈Icc 1 K) (i : ℕ) :
    (C (uniformizer ω ^ (QZeta3.clusterRowWeight (clusterMultiplicity K d r) j +
        QZeta3.clusterColWeight (clusterMultiplicity K d s) k) *
        ((movingClusterPoly (RatFunc.X : RatFunc 𝕜) (RatFunc.C ω) K d r j).eval (RatFunc.X^a) *
          (movingClusterPoly (RatFunc.X : RatFunc 𝕜) (RatFunc.C ω) K d s k).eval (RatFunc.X^a) /
          (RatFunc.X^a * (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X^a)))) *
      (X-C (S (RatFunc.X : RatFunc 𝕜) a))).coeff i ∈ regularAt ω := by
  by_cases har : a%d = r
  · by_cases has : a%d = s
    · have hrs : s=r := has.symm.trans har
      rw [hrs]
      apply proper_term_coeff_mem ω hω0 K a ha _ (j+k)
      · exact product_div_uniformizer_pow_mem ω _ _ j k
          (movingClusterPoly_eval_div_mem hω K r j a har)
          (movingClusterPoly_eval_div_mem hω K r k a har)
      · rw [collisionCount_eq_clusterMultiplicity_sub_one hω hd K a ha, har]
        have hpos : 0<clusterMultiplicity K d r := Finset.card_pos.mpr
          ⟨a, Finset.mem_filter.mpr ⟨ha, har⟩⟩
        have hweight := QZeta3.cluster_weights_proper (clusterMultiplicity K d r) j k
        omega
    · rw [movingClusterPoly_eval_zero RatFunc.X (RatFunc.C ω) K d s k a ha has]
      simp
  · rw [movingClusterPoly_eval_zero RatFunc.X (RatFunc.C ω) K d r j a ha har]
    simp

end QZeta3.Generic
