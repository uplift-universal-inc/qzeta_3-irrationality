import QZeta3.HighClusterBasis

/-! # Proper residues in the refined high-order cluster basis -/

open Polynomial Finset

namespace QZeta3.Generic

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Tails before the first cyclotomic collision are regular. -/
theorem S_mem_regularAt_before_order {ω : 𝕜} {d : ℕ}
    (hω : IsPrimitiveRoot ω d) (a : ℕ) (ha : a<d) :
    S (RatFunc.X : RatFunc 𝕜) a ∈ regularAt ω := by
  apply S_mem_regularAt_of_pow_ne_one
  intro b hb hpow
  have hbd := (hω.pow_eq_one_iff_dvd b).mp hpow
  have hb0 : 0<b := (Finset.mem_Icc.mp hb).1
  have hba : b≤a := (Finset.mem_Icc.mp hb).2
  have := Nat.le_of_dvd hb0 hbd
  omega

/-- The complement kills every residue from another cluster. -/
theorem shiftedCluster_eval_zero (z : 𝕜) (K d r j a : ℕ)
    (ha : a∈Icc 1 K) (har : a%d≠r) :
    (movingClusterComplement z K d r * (X-C (z^(r+d)))^j).eval (z^a)=0 := by
  rw [Polynomial.eval_mul]
  have hc : (movingClusterComplement z K d r).eval (z^a)=0 := by
    unfold movingClusterComplement
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨ha,har⟩)
    simp
  rw [hc, zero_mul]

/-- Each weighted proper residue in the high-order basis is regular. -/
theorem highCluster_proper_term_mem {ω : 𝕜} {K d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 0<d) (hdK : d≤K) (hhi : K<2*d)
    (hω0 : ω≠0) (u v : ClusterIndex K d) (a : ℕ) (ha : a∈Icc 1 K) (i : ℕ) :
    (C (uniformizer ω ^ (highRowWeight K d u + highColWeight K d v) *
        (((highClusterPoly ω K d u).map (regularAt ω).subtype).eval (RatFunc.X^a) *
          ((highClusterPoly ω K d v).map (regularAt ω).subtype).eval (RatFunc.X^a) /
          (RatFunc.X^a * (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X^a)))) *
      (X-C (S (RatFunc.X : RatFunc 𝕜) a))).coeff i ∈ regularAt ω := by
  rw [highClusterPoly_subtype, highClusterPoly_subtype]
  by_cases har : a%d=u.1.val
  · by_cases has : a%d=v.1.val
    · have hrs : v.1.val=u.1.val := has.symm.trans har
      simp only [hrs]
      have hmu := u.2.isLt
      have hmv := v.2.isLt
      simp only [hrs] at hmv
      have hcount := collisionCount_eq_clusterMultiplicity_sub_one hω hd K a ha
      rw [har] at hcount
      have hm := clusterMultiplicity_high hd hdK hhi u.1.isLt
      have hV := movingClusterComplement_coeff_mem (regularAt ω) RatFunc.X
        (base_mem_regularAt ω) K d u.1.val
      have hnode : (a=u.1.val ∧ 0<u.1.val) ∨
          (a=u.1.val+d ∧ u.1.val≤K-d) :=
        (mem_clusterIndices_high hd hdK hhi u.1.isLt).mp
          (Finset.mem_filter.mpr ⟨ha,har⟩)
      have hpow : ω^a=ω^(u.1.val+d) := by
        rw [pow_eq_pow_mod a hω.pow_eq_one, har, pow_add, hω.pow_eq_one, mul_one]
      have hN := product_div_uniformizer_pow_mem ω _ _ u.2.val v.2.val
        (shifted_cluster_numerator_eval_div_mem ω a (u.1.val+d) u.2.val hpow _ hV)
        (shifted_cluster_numerator_eval_div_mem ω a (u.1.val+d) v.2.val hpow _ hV)
      rcases hnode with ⟨haroot,hrpos⟩ | ⟨haupper,hrK⟩
      · apply proper_term_coeff_mem_of_tail_regular ω hω0 K a ha _ (u.2.val+v.2.val)
        · exact hN
        · apply S_mem_regularAt_before_order hω
          simpa [haroot] using u.1.isLt
        · rw [hcount]
          simp only [highRowWeight, highColWeight, hrs]
          simp only [hm]
          split_ifs <;> omega
      · by_cases huv : 0<u.2.val+v.2.val
        · subst a
          have hz := double_cluster_upper_proper_zero K (u.1.val+d)
            u.2.val v.2.val huv (movingClusterComplement (RatFunc.X : RatFunc 𝕜) K d u.1.val)
          rw [Polynomial.C_mul, mul_assoc, hz, mul_zero, Polynomial.coeff_zero]
          exact (regularAt ω).zero_mem
        · have hu0 : u.2.val=0 := by omega
          have hv0 : v.2.val=0 := by omega
          apply proper_term_coeff_mem ω hω0 K a ha _ (u.2.val+v.2.val)
          · exact hN
          · rw [hcount]
            simp only [highRowWeight, highColWeight, hrs, hu0, hv0]
            simp only [hm]
            split_ifs <;> omega
    · rw [shiftedCluster_eval_zero RatFunc.X K d v.1.val v.2.val a ha has]
      simp
  · rw [shiftedCluster_eval_zero RatFunc.X K d u.1.val u.2.val a ha har]
    simp

/-- The full proper part has regular coefficients after the refined row/column scaling. -/
theorem highCluster_proper_sum_mem {ω : 𝕜} {K d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 0<d) (hdK : d≤K) (hhi : K<2*d)
    (hω0 : ω≠0) (u v : ClusterIndex K d) (i : ℕ) :
    (C (uniformizer ω ^ (highRowWeight K d u+highColWeight K d v)) *
      (∑ a∈Icc 1 K,
        C ((((highClusterPoly ω K d u).map (regularAt ω).subtype) *
          ((highClusterPoly ω K d v).map (regularAt ω).subtype)).eval (RatFunc.X^a) /
          (RatFunc.X^a * (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X^a))) *
          (X-C (S (RatFunc.X : RatFunc 𝕜) a)))).coeff i ∈ regularAt ω := by
  rw [Finset.mul_sum, Polynomial.finsetSum_coeff]
  apply (regularAt ω).sum_mem
  intro a ha
  simpa only [← mul_assoc, ← Polynomial.C_mul, Polynomial.eval_mul]
    using highCluster_proper_term_mem hω hd hdK hhi hω0 u v a ha i

end QZeta3.Generic
