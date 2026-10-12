import QZeta3.LocalGramBounds
import QZeta3.LocalClusterTransport
import QZeta3.HighProperEntries

/-! # The high-order cyclotomic bound for the actual determinant

The moving upper-node basis clears the proper residues. The sole remaining
polynomial moment contributes at most its rank, which fits in the stated exponent.
-/

open Polynomial Finset Matrix

namespace QZeta3.Generic

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- In the high range, the refined cluster weights and the polynomial-moment
rank correction clear every coefficient of the original determinant. -/
theorem high_Delta_scaled_coeff_mem {ω : 𝕜} {K d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 0 < d) (hdK : d ≤ K)
    (hhi : K < 2*d) (hω0 : ω ≠ 0) (i : ℕ) :
    uniformizer ω ^ cApp K d * (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i ∈
      regularAt ω := by
  classical
  let β := highClusterCenter ω d
  let e := (clusterEquivFin K d hd).symm
  let G := transportClusterPoly ω K d hd β
  let r : Fin K → ℕ := fun a => highRowWeight K d (e a)
  let c : Fin K → ℕ := fun a => highColWeight K d (e a)
  have hGdegree := transportClusterPoly_degree_lt ω K d hd β
  have hGcoeff := transportClusterPoly_coeff_mem ω K d hd β
  have hproper (a b : Fin K) : C (uniformizer ω^(r a+c b)) *
      (∑ t ∈ Icc 1 K, C ((G a*G b).eval (RatFunc.X^t) /
        (RatFunc.X^t * (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X^t))) *
        (X-C (S (RatFunc.X : RatFunc 𝕜) t))) ∈
      Polynomial.liftsRing (regularAt ω).subtype := by
    apply (coeff_mem_iff_lifts (regularAt ω) _).mp
    intro j
    simpa only [G, r, c, β, e, transportClusterPoly, highClusterPoly] using
      highCluster_proper_sum_mem hω hd hdK hhi hω0 (e a) (e b) j
  have hdet := high_gram_det_mem hω hω0 hhi G hGdegree hGcoeff r c hproper
  have hβ (a : Fin d) : localEval ω (β a) = ω^a.val :=
    localEval_highClusterCenter hω.pow_eq_one a
  have hU0 := transportCluster_det_ne_zero hω hd hdK β hβ
  have hUinv := transportCluster_det_inv_mem hω hd hdK β hβ
  have hcleared := Delta_scaled_coeff_mem_of_gram ω hω0 K
    ((∑ a, r a)+(∑ a, c a)+(K-d-1)) G hGdegree hU0 hUinv hdet i
  have hcost : (∑ a, r a)+(∑ a, c a)+(K-d-1) ≤ cApp K d := by
    dsimp only [r, c]
    rw [e.sum_comp (highRowWeight K d), e.sum_comp (highColWeight K d)]
    exact sum_high_weights_add_rank_le_cApp hd hdK hhi (by omega)
  exact uniformizer_pow_mul_mem_of_le ω _ hcost hcleared

end QZeta3.Generic
