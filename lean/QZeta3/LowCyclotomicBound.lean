import QZeta3.LocalGramBounds
import QZeta3.LocalClusterTransport

/-! The complete low-order local cyclotomic pole bound. -/
open Polynomial Finset
namespace QZeta3.Generic
variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

noncomputable def lowClusterCenter (ω : 𝕜) (d : ℕ) (r : Fin d) : regularAt ω :=
  ⟨algebraMap 𝕜[X] (RatFunc 𝕜) (C (ω^r.val)), polynomial_mem_regularAt ω _⟩

omit [CharZero 𝕜] in
@[simp] theorem localEval_lowClusterCenter (ω : 𝕜) (d : ℕ) (r : Fin d) :
    localEval ω (lowClusterCenter ω d r)=ω^r.val := by
  rw [lowClusterCenter, localEval_polynomial, Polynomial.eval_C]

omit [CharZero 𝕜] in
theorem transportClusterPoly_low_eq (ω : 𝕜) (K d : ℕ) (hd : 0<d) (i : Fin K) :
    transportClusterPoly ω K d hd (lowClusterCenter ω d) i =
      movingClusterPoly (RatFunc.X : RatFunc 𝕜) (RatFunc.C ω) K d
        ((clusterEquivFin K d hd).symm i).1.val ((clusterEquivFin K d hd).symm i).2.val := by
  rw [transportClusterPoly_eq]
  simp only [lowClusterCenter, RatFunc.algebraMap_C, movingClusterPoly, map_pow]

/-- Every coefficient of the determinant has at most the prescribed low-order pole. -/
theorem low_cyclotomic_bound {ω : 𝕜} {K d : ℕ} (hω : IsPrimitiveRoot ω d)
    (hd : 0<d) (hdK : d≤K) (hlo : 2*d≤K) (i : ℕ) :
    uniformizer ω^cApp K d * (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i∈regularAt ω := by
  have hω0 : ω≠0 := hω.ne_zero (by omega)
  let β := lowClusterCenter ω d
  let e := (clusterEquivFin K d hd).symm
  let G := transportClusterPoly ω K d hd β
  let r := fun i : Fin K => clusterRowWeight (clusterMultiplicity K d (e i).1.val) (e i).2.val
  let c := fun i : Fin K => clusterColWeight (clusterMultiplicity K d (e i).1.val) (e i).2.val
  have hG : G=fun i : Fin K => movingClusterPoly (RatFunc.X : RatFunc 𝕜)
      (RatFunc.C ω) K d (e i).1.val (e i).2.val := by
    funext i
    exact transportClusterPoly_low_eq ω K d hd i
  have hdet : C (uniformizer ω)^((∑ i, r i)+(∑ i, c i)) *
      (unnormalizedGram RatFunc.X K G).det∈Polynomial.liftsRing (regularAt ω).subtype := by
    rw [hG]
    exact low_gram_det_mem hω hd hω0 e
  have hcoeff := Delta_scaled_coeff_mem_of_gram ω hω0 K ((∑ i, r i)+(∑ i, c i)) G
    (transportClusterPoly_degree_lt ω K d hd β)
    (transportCluster_det_ne_zero hω hd hdK β (localEval_lowClusterCenter ω d))
    (transportCluster_det_inv_mem hω hd hdK β (localEval_lowClusterCenter ω d)) hdet i
  exact uniformizer_pow_mul_mem_of_le ω _ (low_weight_cost_le hd hlo e) hcoeff

end QZeta3.Generic
