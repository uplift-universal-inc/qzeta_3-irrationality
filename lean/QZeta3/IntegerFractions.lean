import QZeta3.GenericMoments
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Div

/-!
# Integral descent for fractions with monic integer denominators

The generic determinant is constructed inside this subring. If local pole
clearing makes such a fraction a polynomial, monic polynomial division
descends that polynomial back to integer coefficients.
-/

open Polynomial

namespace QZeta3.Generic

variable {𝕜 : Type*} [Field 𝕜]

noncomputable def intPolynomialMap : ℤ[X] →+* RatFunc 𝕜 :=
  (algebraMap 𝕜[X] (RatFunc 𝕜)).comp (Polynomial.mapRingHom (Int.castRingHom 𝕜))

theorem intPolynomialMap_apply (f : ℤ[X]) :
    intPolynomialMap (𝕜 := 𝕜) f =
      algebraMap 𝕜[X] (RatFunc 𝕜) (f.map (Int.castRingHom 𝕜)) := rfl

theorem intPolynomialMap_ne_zero {f : ℤ[X]} (hf : f.Monic) :
    intPolynomialMap (𝕜 := 𝕜) f ≠ 0 :=
  RatFunc.algebraMap_ne_zero (hf.map (Int.castRingHom 𝕜)).ne_zero

def IsIntegerMonicFraction (x : RatFunc 𝕜) : Prop :=
  ∃ A B : ℤ[X], B.Monic ∧ x = intPolynomialMap A / intPolynomialMap B

def integerMonicFractions : Subring (RatFunc 𝕜) where
  carrier := {x | IsIntegerMonicFraction x}
  zero_mem' := ⟨0, 1, monic_one, by simp⟩
  one_mem' := ⟨1, 1, monic_one, by simp⟩
  neg_mem' := by
    rintro x ⟨A, B, hB, rfl⟩
    exact ⟨-A, B, hB, by rw [map_neg, neg_div]⟩
  add_mem' := by
    rintro x y ⟨A, B, hB, rfl⟩ ⟨C, D, hD, rfl⟩
    refine ⟨A * D + B * C, B * D, hB.mul hD, ?_⟩
    rw [map_add, map_mul, map_mul, map_mul]
    exact div_add_div _ _ (intPolynomialMap_ne_zero (𝕜 := 𝕜) hB)
      (intPolynomialMap_ne_zero (𝕜 := 𝕜) hD)
  mul_mem' := by
    rintro x y ⟨A, B, hB, rfl⟩ ⟨C, D, hD, rfl⟩
    exact ⟨A * C, B * D, hB.mul hD, by rw [map_mul, map_mul, div_mul_div_comm]⟩

theorem integerPolynomial_mem (A : ℤ[X]) :
    intPolynomialMap (𝕜 := 𝕜) A ∈ integerMonicFractions :=
  ⟨A, 1, monic_one, by simp⟩

theorem inverse_monic_mem (B : ℤ[X]) (hB : B.Monic) :
    (intPolynomialMap (𝕜 := 𝕜) B)⁻¹ ∈ integerMonicFractions :=
  ⟨1, B, hB, by simp⟩

/-- All generic moments are built from integer fractions with monic denominators. -/
theorem integerMonicFraction_localization (K : ℕ) :
    LocalizationData (integerMonicFractions (𝕜 := 𝕜)) RatFunc.X K where
  base_mem := by
    simpa [intPolynomialMap] using integerPolynomial_mem (𝕜 := 𝕜) X
  inv_base_mem := by
    simpa [intPolynomialMap] using inverse_monic_mem (𝕜 := 𝕜) X monic_X
  inv_geom_mem n hn := by
    have hmonic : (X ^ n - 1 : ℤ[X]).Monic :=
      Polynomial.monic_X_pow_sub_C 1 (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hn).1)
    have h := inverse_monic_mem (𝕜 := 𝕜) (X ^ n - 1) hmonic
    simpa [intPolynomialMap] using h

theorem Delta_coeff_integerMonicFraction (K i : ℕ) :
    (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i ∈ integerMonicFractions :=
  (integerMonicFraction_localization (𝕜 := 𝕜) K).Delta_coeff_mem i

variable [CharZero 𝕜]

/-- Gauss descent in the exact form needed after clearing finite poles. -/
theorem polynomial_of_integerMonicFraction (x : RatFunc 𝕜)
    (hx : x ∈ integerMonicFractions) (P : 𝕜[X])
    (hP : x = algebraMap 𝕜[X] (RatFunc 𝕜) P) :
    ∃ A : ℤ[X], x = intPolynomialMap A := by
  obtain ⟨A, B, hB, hfrac⟩ := hx
  have he : (A.map (Int.castRingHom 𝕜)) = (B.map (Int.castRingHom 𝕜)) * P := by
    apply RatFunc.algebraMap_injective 𝕜
    rw [map_mul, ← hP, hfrac, ← intPolynomialMap_apply, ← intPolynomialMap_apply]
    field_simp [intPolynomialMap_ne_zero hB]
  have hdiv : B.map (Int.castRingHom 𝕜) ∣ A.map (Int.castRingHom 𝕜) := ⟨P, he⟩
  have hdivZ : B ∣ A :=
    (Polynomial.map_dvd_map (Int.castRingHom 𝕜) (Int.cast_injective) hB).mp hdiv
  obtain ⟨Q, hQ⟩ := hdivZ
  refine ⟨Q, ?_⟩
  rw [hfrac, hQ, map_mul, mul_div_cancel_left₀ _ (intPolynomialMap_ne_zero hB)]

/-- Clearing the pole at zero as well gives a Laurent integer polynomial. -/
theorem laurent_of_integerMonicFraction (x : RatFunc 𝕜)
    (hx : x ∈ integerMonicFractions) (m : ℕ) (P : 𝕜[X])
    (hP : intPolynomialMap (𝕜 := 𝕜) (X ^ m) * x = algebraMap 𝕜[X] (RatFunc 𝕜) P) :
    ∃ A : ℤ[X], intPolynomialMap (𝕜 := 𝕜) (X ^ m) * x = intPolynomialMap A :=
  polynomial_of_integerMonicFraction _
    (integerMonicFractions.mul_mem (integerPolynomial_mem _) hx) P hP

end QZeta3.Generic
