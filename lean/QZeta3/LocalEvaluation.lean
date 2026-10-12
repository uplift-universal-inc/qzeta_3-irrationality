import QZeta3.CyclotomicLocal

/-! # Evaluation on the local ring of rational functions -/

open Polynomial

namespace QZeta3.Generic

variable {𝕜 : Type*} [Field 𝕜]

theorem regularAt_iff_denom_eval_ne_zero (ω : 𝕜) (x : RatFunc 𝕜) :
    x ∈ regularAt ω ↔ x.denom.eval ω ≠ 0 := by
  constructor
  · rintro ⟨A, B, hB, rfl⟩ hzero
    exact hB (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero
      (RatFunc.denom_div_dvd A B) hzero)
  · intro hx
    exact ⟨x.num, x.denom, hx, (RatFunc.num_div_denom x).symm⟩

noncomputable def localEval (ω : 𝕜) : regularAt ω →+* 𝕜 where
  toFun x := RatFunc.eval (RingHom.id 𝕜) ω x.val
  map_one' := RatFunc.eval_one _ _
  map_zero' := RatFunc.eval_zero _ _
  map_add' x y := by
    apply RatFunc.eval_add
    · simpa only [Polynomial.eval₂_id] using (regularAt_iff_denom_eval_ne_zero ω x.val).mp x.property
    · simpa only [Polynomial.eval₂_id] using (regularAt_iff_denom_eval_ne_zero ω y.val).mp y.property
  map_mul' x y := by
    apply RatFunc.eval_mul
    · simpa only [Polynomial.eval₂_id] using (regularAt_iff_denom_eval_ne_zero ω x.val).mp x.property
    · simpa only [Polynomial.eval₂_id] using (regularAt_iff_denom_eval_ne_zero ω y.val).mp y.property

@[simp] theorem localEval_apply (ω : 𝕜) (x : regularAt ω) :
    localEval ω x = RatFunc.eval (RingHom.id 𝕜) ω x.val := rfl

@[simp] theorem localEval_polynomial (ω : 𝕜) (P : 𝕜[X]) :
    localEval ω ⟨algebraMap 𝕜[X] (RatFunc 𝕜) P, polynomial_mem_regularAt ω P⟩ = P.eval ω := by
  simp

theorem inv_mem_regularAt_of_eval_ne_zero (ω : 𝕜) (x : RatFunc 𝕜)
    (hx : RatFunc.eval (RingHom.id 𝕜) ω x ≠ 0) : x⁻¹ ∈ regularAt ω := by
  have hn : x.num.eval ω ≠ 0 := by
    intro hn
    apply hx
    simp [RatFunc.eval, hn]
  refine ⟨x.denom, x.num, hn, ?_⟩
  conv_lhs => rw [← RatFunc.num_div_denom x]
  rw [inv_div]

/-- A local element with nonzero residue is a unit in the local ring. -/
theorem isUnit_of_localEval_ne_zero (ω : 𝕜) (x : regularAt ω)
    (hx : localEval ω x ≠ 0) : IsUnit x := by
  have hxi := inv_mem_regularAt_of_eval_ne_zero ω x.val hx
  have hx0 : x.val ≠ 0 := by
    intro hx0
    apply hx
    simp [localEval, hx0]
  refine ⟨⟨x, ⟨x.val⁻¹, hxi⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    exact mul_inv_cancel₀ hx0
  · apply Subtype.ext
    exact inv_mul_cancel₀ hx0

end QZeta3.Generic
