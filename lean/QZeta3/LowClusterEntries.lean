import QZeta3.MovingProper

/-! # Complete local low-order cluster-entry clearing -/
open Polynomial Finset
namespace QZeta3.Generic

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The complete polynomial-quotient and proper-fraction entry is cleared by the
integer cluster weights. This is the actual local matrix estimate of §4. -/
theorem movingCluster_scaled_entry_formula_mem {ω : 𝕜} {d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 0<d) (hω0 : ω≠0) (K r s j k : ℕ) :
    let G := movingClusterPoly (RatFunc.X : RatFunc 𝕜) (RatFunc.C ω) K d r j
    let H := movingClusterPoly (RatFunc.X : RatFunc 𝕜) (RatFunc.C ω) K d s k
    let w := QZeta3.clusterRowWeight (clusterMultiplicity K d r) j +
      QZeta3.clusterColWeight (clusterMultiplicity K d s) k
    ∀ i, (C (uniformizer ω ^ w) *
      (C (Lpoly (RatFunc.X : RatFunc 𝕜) (G*H /ₘ F RatFunc.X K)) -
        ∑ a ∈ Icc 1 K, C ((G*H).eval (RatFunc.X^a) /
          (RatFunc.X^a * (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X^a))) *
          (X-C (S (RatFunc.X : RatFunc 𝕜) a)))).coeff i ∈ regularAt ω := by
  intro G H w i
  let R := regularAt ω
  let T := Polynomial.liftsRing R.subtype
  have hC (x : RatFunc 𝕜) (hx : x∈R) : C x ∈T :=
    (Polynomial.lifts_iff_liftsRing _ _).mp
      (Polynomial.C'_mem_lifts ⟨⟨x,hx⟩,rfl⟩)
  have hconst : RatFunc.C ω ∈R := by
    simpa only [RatFunc.algebraMap_C] using polynomial_mem_regularAt ω (C ω)
  have hG : ∀ i, G.coeff i ∈R :=
    movingClusterPoly_coeff_mem R RatFunc.X (RatFunc.C ω)
      (base_mem_regularAt ω) hconst K d r j
  have hH : ∀ i, H.coeff i ∈R :=
    movingClusterPoly_coeff_mem R RatFunc.X (RatFunc.C ω)
      (base_mem_regularAt ω) hconst K d s k
  have hGH : ∀ i, (G*H).coeff i ∈R := (coeff_mem_iff_lifts R _).mpr
    (T.mul_mem ((coeff_mem_iff_lifts R _).mp hG) ((coeff_mem_iff_lifts R _).mp hH))
  have hQ := uniformizer_mul_quotient_moment_mem ω hω0 K (G*H) hGH
  have hw : 1≤w := QZeta3.cluster_weights_polynomial _ _ _ _
  have hQw : uniformizer ω ^ w * Lpoly (RatFunc.X : RatFunc 𝕜) (G*H /ₘ F RatFunc.X K) ∈R := by
    have h := R.mul_mem (R.pow_mem (uniformizer_mem ω) (w-1)) hQ
    convert h using 1
    rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hw]
  have hpoly : C (uniformizer ω ^ w) * C (Lpoly (RatFunc.X : RatFunc 𝕜)
      (G*H /ₘ F RatFunc.X K)) ∈T := by
    rw [← map_mul]
    exact hC _ hQw
  have hproper (a : ℕ) (ha : a∈Icc 1 K) :
      C (uniformizer ω ^ w) *
        (C ((G*H).eval (RatFunc.X^a) /
          (RatFunc.X^a * (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X^a))) *
          (X-C (S (RatFunc.X : RatFunc 𝕜) a))) ∈T := by
    apply (coeff_mem_iff_lifts R _).mp
    intro l
    rw [← mul_assoc, ← map_mul, Polynomial.eval_mul]
    exact movingCluster_proper_term_mem hω hd hω0 K r s j k a ha l
  apply (coeff_mem_iff_lifts R _).mpr
  rw [mul_sub, Finset.mul_sum]
  exact T.sub_mem hpoly (T.sum_mem hproper)

end QZeta3.Generic
