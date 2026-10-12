import QZeta3.LocalEvaluation
import Mathlib.FieldTheory.IsAlgClosed.Basic

open Polynomial

namespace QZeta3.Generic

variable {𝕜 : Type*} [Field 𝕜]

/-- A local uniformizer bound controls the multiplicity of the reduced denominator. -/
theorem denom_rootMultiplicity_le_of_regular (ω : 𝕜) (x : RatFunc 𝕜) (c : ℕ)
    (h : uniformizer ω ^ c * x ∈ regularAt ω) :
    rootMultiplicity ω x.denom ≤ c := by
  obtain ⟨f, g, hg, he⟩ := h
  let u : 𝕜[X] := (X - C ω)^c
  have hu : u ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero ω)
  have hg0 : g ≠ 0 := by intro hzero; exact hg (by simp [hzero])
  have hug : u*g ≠ 0 := mul_ne_zero hu hg0
  have hgm : algebraMap 𝕜[X] (RatFunc 𝕜) g ≠ 0 := RatFunc.algebraMap_ne_zero hg0
  have hugm : algebraMap 𝕜[X] (RatFunc 𝕜) (u*g) ≠ 0 := RatFunc.algebraMap_ne_zero hug
  have hpresent : x = algebraMap 𝕜[X] (RatFunc 𝕜) f /
      algebraMap 𝕜[X] (RatFunc 𝕜) (u*g) := by
    apply (eq_div_iff hugm).mpr
    have hh := (eq_div_iff hgm).mp he
    calc x * algebraMap 𝕜[X] (RatFunc 𝕜) (u*g) =
        (uniformizer ω^c*x) * algebraMap 𝕜[X] (RatFunc 𝕜) g := by
          simp only [map_mul, u, map_pow, uniformizer]
          ring
      _ = _ := hh
  have hdvd : x.denom ∣ u*g := (RatFunc.denom_dvd hug).mpr ⟨f, hpresent⟩
  have hb := rootMultiplicity_le_rootMultiplicity_of_dvd hug hdvd ω
  rw [rootMultiplicity_mul hug] at hb
  have hgu : rootMultiplicity ω g = 0 := rootMultiplicity_eq_zero hg
  simpa only [u, rootMultiplicity_X_sub_C_pow, hgu, add_zero] using hb

/-- Multiplication by a polynomial clears a rational function exactly when it is divisible
by the reduced denominator. -/
theorem exists_polynomial_multiple_of_denom_dvd (x : RatFunc 𝕜) (D : 𝕜[X])
    (hD : x.denom ∣ D) :
    ∃ P : 𝕜[X], algebraMap 𝕜[X] (RatFunc 𝕜) D * x =
      algebraMap 𝕜[X] (RatFunc 𝕜) P := by
  obtain ⟨A, hA⟩ := hD
  refine ⟨A*x.num, ?_⟩
  rw [hA, map_mul, map_mul]
  have hden : algebraMap 𝕜[X] (RatFunc 𝕜) x.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero x)
  conv_lhs => arg 2; rw [← RatFunc.num_div_denom x]
  field_simp

/-- Over an algebraically closed field, controlling every nonzero pole clears all denominators
after multiplication by a sufficient power of the base variable. -/
theorem exists_polynomial_multiple_of_nonzero_pole_bounds [IsAlgClosed 𝕜]
    (x : RatFunc 𝕜) (D : 𝕜[X])
    (hlocal : ∀ ω : 𝕜, ω ≠ 0 → rootMultiplicity ω x.denom ≤ rootMultiplicity ω D) :
    ∃ m : ℕ, ∃ P : 𝕜[X], algebraMap 𝕜[X] (RatFunc 𝕜) (X^m * D) * x =
      algebraMap 𝕜[X] (RatFunc 𝕜) P := by
  classical
  by_cases hD : D = 0
  · exact ⟨0, 0, by simp [hD]⟩
  let m := rootMultiplicity (0 : 𝕜) x.denom
  have hXD : (X : 𝕜[X])^m * D ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hD
  have hmul : x.denom ∣ (X : 𝕜[X])^m * D := by
    apply (IsAlgClosed.splits x.denom).dvd_of_roots_le_roots (RatFunc.denom_ne_zero x)
    apply Multiset.le_iff_count.mpr
    intro ω
    simp only [Polynomial.count_roots]
    rw [rootMultiplicity_mul hXD]
    by_cases hω : ω = 0
    · subst ω
      have hm : rootMultiplicity (0 : 𝕜) ((X : 𝕜[X])^m) = m := by
        simpa only [map_zero, sub_zero] using rootMultiplicity_X_sub_C_pow (0 : 𝕜) m
      rw [hm]
      exact Nat.le_add_right _ _
    · exact (hlocal ω hω).trans (Nat.le_add_left _ _)
  obtain ⟨P, hP⟩ := exists_polynomial_multiple_of_denom_dvd x (X^m*D) hmul
  exact ⟨m, P, hP⟩

theorem exists_polynomial_multiple_of_regular_uniformizers [IsAlgClosed 𝕜]
    (x : RatFunc 𝕜) (D : 𝕜[X])
    (hlocal : ∀ ω : 𝕜, ω ≠ 0 →
      uniformizer ω ^ rootMultiplicity ω D * x ∈ regularAt ω) :
    ∃ m : ℕ, ∃ P : 𝕜[X], algebraMap 𝕜[X] (RatFunc 𝕜) (X^m * D) * x =
      algebraMap 𝕜[X] (RatFunc 𝕜) P :=
  exists_polynomial_multiple_of_nonzero_pole_bounds x D
    (fun ω hω => denom_rootMultiplicity_le_of_regular ω x _ (hlocal ω hω))

end QZeta3.Generic
