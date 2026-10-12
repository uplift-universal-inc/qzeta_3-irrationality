import QZeta3.NonvanishingAlgebra
import Mathlib.Analysis.Meromorphic.Order

/-!
# Meromorphic input for interpolation normality

A meromorphic error at infinity which is not the zero germ and tends to
zero has a first nonzero Laurent coefficient.  This supplies the abstract
nonflatness hypothesis in `frequently_nonsingular_moment_matrix`.
-/

open Polynomial Filter Topology Asymptotics

namespace QZeta3.NonvanishingAlgebra

/-- Inversion takes positive infinity into a punctured neighborhood of zero. -/
theorem inv_tendsto_punctured_zero :
    Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_inv_atTop_zero, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simpa using inv_ne_zero (ne_of_gt hx)

/-- A polynomial evaluated at the inverse variable is meromorphic at zero. -/
theorem polynomial_eval_inv_meromorphic (P : ℝ[X]) :
    MeromorphicAt (fun u : ℝ => P.eval u⁻¹) 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      convert hP.add hQ using 1
      ext u
      simp
  | monomial n c =>
      convert (MeromorphicAt.const c 0).mul (((MeromorphicAt.id (0 : ℝ)).inv).pow n) using 1
      ext u
      simp

/-- A meromorphic function with a nonzero germ at infinity and a vanishing
limit has a finite Laurent leading term. -/
theorem exists_laurent_limit_of_meromorphic_inv (E : ℝ → ℝ)
    (hmeromorphic : MeromorphicAt (fun u : ℝ => E u⁻¹) 0)
    (hnonzero : ¬ ∀ᶠ u : ℝ in 𝓝[≠] 0, E u⁻¹ = 0)
    (hlimit : Tendsto E atTop (𝓝 0)) :
    ∃ h : ℕ, ∃ c : ℝ, c ≠ 0 ∧
      Tendsto (fun x : ℝ => x ^ h * E x) atTop (𝓝 c) := by
  let f : ℝ → ℝ := fun u => E u⁻¹
  have htop : meromorphicOrderAt f 0 ≠ ⊤ := by
    exact fun h => hnonzero (meromorphicOrderAt_eq_top_iff.mp h)
  have hinv := inv_tendsto_punctured_zero
  have hlimf : Tendsto (fun x : ℝ => f x⁻¹) atTop (𝓝 0) := by
    simpa [f] using hlimit
  have hnonneg : 0 ≤ meromorphicOrderAt f 0 := by
    by_contra h
    have hnegative : meromorphicOrderAt f 0 < 0 := lt_of_not_ge h
    have hdiverges := (tendsto_cobounded_of_meromorphicOrderAt_neg hnegative).comp hinv
    have hnorm : Tendsto (fun x : ℝ => ‖f x⁻¹‖) atTop atTop :=
      tendsto_norm_atTop_iff_cobounded.mpr hdiverges
    exact not_tendsto_atTop_of_tendsto_nhds hlimf.norm hnorm
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp htop
  have hk0 : 0 ≤ k := by simpa [← hk] using hnonneg
  obtain ⟨g, hga, hg0, hfactor⟩ :=
    (meromorphicOrderAt_eq_int_iff hmeromorphic).mp hk.symm
  refine ⟨k.toNat, g 0, hg0, ?_⟩
  have hcont : Tendsto (fun x : ℝ => g x⁻¹) atTop (𝓝 (g 0)) :=
    hga.continuousAt.tendsto.comp tendsto_inv_atTop_zero
  apply hcont.congr'
  filter_upwards [hinv.eventually hfactor, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  have hxn : x ≠ 0 := ne_of_gt hxpos
  have hknat : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
  simp only [sub_zero, smul_eq_mul, inv_inv] at hx
  rw [← hknat, zpow_natCast] at hx
  rw [hx, ← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hxn), one_mul]

/-- Meromorphicity at infinity and exclusion of rational germs supply all
nonflatness hypotheses of the interpolation normality theorem. -/
theorem nonflat_of_meromorphic_nonrational (F : ℝ → ℝ)
    (hmeromorphic : MeromorphicAt (fun u : ℝ => F u⁻¹) 0)
    (hnonrational : ∀ P Q : ℝ[X], Q ≠ 0 →
      ¬ ∀ᶠ x : ℝ in atTop, F x * Q.eval x - P.eval x = 0)
    (P Q : ℝ[X]) (hQ : Q ≠ 0)
    (hlimit : Tendsto (fun x => F x * Q.eval x - P.eval x) atTop (𝓝 0)) :
    ∃ h : ℕ, ∃ c : ℝ, c ≠ 0 ∧
      Tendsto (fun x : ℝ => x ^ h * (F x * Q.eval x - P.eval x)) atTop (𝓝 c) := by
  apply exists_laurent_limit_of_meromorphic_inv
    (fun x => F x * Q.eval x - P.eval x)
    ((hmeromorphic.mul (polynomial_eval_inv_meromorphic Q)).sub
      (polynomial_eval_inv_meromorphic P)) _ hlimit
  intro hzero
  apply hnonrational P Q hQ
  simpa using inv_tendsto_punctured_zero.eventually hzero

/-- The general analytic normality theorem, now phrased directly in terms
of a nonrational meromorphic Cauchy transform and orthogonal interpolants. -/
theorem frequently_nonsingular_of_meromorphic_nonrational
    (F : ℝ → ℝ) (t : ℕ → ℝ)
    (ht : Function.Injective t) (htop : Tendsto t atTop atTop)
    (L : ℕ → (ℝ[X] →ₗ[ℝ] ℝ))
    (hmeromorphic : MeromorphicAt (fun u : ℝ => F u⁻¹) 0)
    (hnonrational : ∀ P Q : ℝ[X], Q ≠ 0 →
      ¬ ∀ᶠ x : ℝ in atTop, F x * Q.eval x - P.eval x = 0)
    (hinterpolant : ∀ n, 0 < n → ∀ Q : ℝ[X], Q ≠ 0 → Q.natDegree < n →
      (∀ j : Fin n, L n (Polynomial.X ^ j.val * Q) = 0) →
      ∃ P : ℝ[X],
        Tendsto (fun x => F x * Q.eval x - P.eval x) atTop (𝓝 0) ∧
        ∀ a, a < n → F (t a) * Q.eval (t a) - P.eval (t a) = 0) :
    ∀ N : ℕ, ∃ n, N ≤ n ∧
      (Matrix.of fun i j : Fin n => L n (Polynomial.X ^ (i.val + j.val))).det ≠ 0 :=
  frequently_nonsingular_moment_matrix F t ht htop L
    (nonflat_of_meromorphic_nonrational F hmeromorphic hnonrational) hinterpolant

end QZeta3.NonvanishingAlgebra
