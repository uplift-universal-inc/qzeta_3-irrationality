import QZeta3.IntegerFractions
import QZeta3.LocalPoleDescent
import QZeta3.GenericEvaluation
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-! # From local cyclotomic pole bounds to integer Laurent coefficients

The only input in this module is the local pole estimate. The descent itself uses
monic integer denominators and checks every nonzero point, including points that
are not roots of unity.
-/

open Polynomial Finset

namespace QZeta3.Generic

/-- The polynomial whose natural-base evaluation is the multiplier `CK`. -/
noncomputable def cyclotomicClearing (K : ℕ) : ℤ[X] :=
  ∏ d ∈ Icc 1 K, (cyclotomic d ℤ) ^ cApp K d

theorem cyclotomicClearing_monic (K : ℕ) : (cyclotomicClearing K).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun d _ => (cyclotomic.monic d ℤ).pow _

@[simp] theorem cyclotomicClearing_eval (p K : ℕ) :
    (cyclotomicClearing K).eval (p : ℤ) = CK p K := by
  simp [cyclotomicClearing, CK, Phi, Polynomial.eval_prod]

variable {𝕜 : Type*} [Field 𝕜]

theorem cyclotomicClearing_map (K : ℕ) :
    (cyclotomicClearing K).map (Int.castRingHom 𝕜) =
      ∏ d ∈ Icc 1 K, (cyclotomic d 𝕜) ^ cApp K d := by
  simp [cyclotomicClearing, Polynomial.map_prod, Polynomial.map_cyclotomic]

/-- The chosen factor provides at least the requested local multiplicity. -/
theorem uniformizer_pow_dvd_cyclotomicClearing (K d : ℕ) (hd : d ∈ Icc 1 K)
    (ω : 𝕜) (hω : IsPrimitiveRoot ω d) :
    (X - C ω) ^ cApp K d ∣ (cyclotomicClearing K).map (Int.castRingHom 𝕜) := by
  rw [cyclotomicClearing_map]
  exact (pow_dvd_pow_of_dvd
    (Polynomial.dvd_iff_isRoot.mpr (hω.isRoot_cyclotomic (mem_Icc.mp hd).1)) _).trans
    (Finset.dvd_prod_of_mem (fun e => (cyclotomic e 𝕜) ^ cApp K e) hd)

/-- Away from zero and geometric roots, every determinant coefficient is regular. -/
theorem Delta_coeff_regular_of_not_root (K i : ℕ) (ω : 𝕜) (hω : ω ≠ 0)
    (hgeom : ∀ n ∈ Icc 1 K, ω ^ n ≠ 1) :
    (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i ∈ regularAt ω := by
  apply LocalizationData.Delta_coeff_mem (R := regularAt ω)
  exact ⟨base_mem_regularAt ω, inv_base_mem_regularAt ω hω,
    fun n hn => inv_geometric_mem_regularAt ω n (hgeom n hn)⟩

/-- Local bounds at primitive roots suffice to clear every nonzero finite pole. -/
theorem cyclotomicClearing_mul_regular (K i : ℕ)
    (hbound : ∀ d ∈ Icc 1 K, ∀ ω : 𝕜, IsPrimitiveRoot ω d →
      uniformizer ω ^ cApp K d * (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i ∈ regularAt ω)
    (ω : 𝕜) (hω : ω ≠ 0) :
    intPolynomialMap (𝕜 := 𝕜) (cyclotomicClearing K) *
      (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i ∈ regularAt ω := by
  classical
  by_cases hroot : ∃ n ∈ Icc 1 K, ω ^ n = 1
  · obtain ⟨n, hn, hpow⟩ := hroot
    have hdvd := orderOf_dvd_of_pow_eq_one hpow
    have hdpos : 0 < orderOf ω := Nat.pos_of_dvd_of_pos hdvd (mem_Icc.mp hn).1
    have hd : orderOf ω ∈ Icc 1 K :=
      mem_Icc.mpr ⟨hdpos, (Nat.le_of_dvd (mem_Icc.mp hn).1 hdvd).trans (mem_Icc.mp hn).2⟩
    obtain ⟨A, hA⟩ := uniformizer_pow_dvd_cyclotomicClearing K (orderOf ω) hd ω
      (IsPrimitiveRoot.orderOf ω)
    have hr := (regularAt ω).mul_mem (polynomial_mem_regularAt ω A)
      (hbound (orderOf ω) hd ω (IsPrimitiveRoot.orderOf ω))
    convert hr using 1
    rw [intPolynomialMap_apply, hA, map_mul, map_pow]
    simp only [uniformizer]
    ring
  · exact (regularAt ω).mul_mem (polynomial_mem_regularAt ω _)
      (Delta_coeff_regular_of_not_root K i ω hω (by simpa using hroot))

variable [CharZero 𝕜]

/-- Global Gauss descent: multiplying by the cyclotomic factor leaves only an integer
Laurent polynomial, with no numerical specializations or unproved integrality assumptions. -/
theorem exists_integer_laurent_of_cyclotomic_bounds [IsAlgClosed 𝕜] (K i : ℕ)
    (hbound : ∀ d ∈ Icc 1 K, ∀ ω : 𝕜, IsPrimitiveRoot ω d →
      uniformizer ω ^ cApp K d * (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i ∈ regularAt ω) :
    ∃ m : ℕ, ∃ A : ℤ[X],
      intPolynomialMap (𝕜 := 𝕜) (X ^ m) *
        (intPolynomialMap (cyclotomicClearing K) *
          (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i) = intPolynomialMap A := by
  let x := intPolynomialMap (𝕜 := 𝕜) (cyclotomicClearing K) *
    (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i
  have hx : x ∈ integerMonicFractions := integerMonicFractions.mul_mem
    (integerPolynomial_mem _) (Delta_coeff_integerMonicFraction K i)
  obtain ⟨m, P, hP⟩ := exists_polynomial_multiple_of_regular_uniformizers x 1
    (fun ω hω => by
      have hmult : rootMultiplicity ω (1 : 𝕜[X]) = 0 := by
        simpa only [map_one] using rootMultiplicity_C (1 : 𝕜) ω
      simpa only [hmult, pow_zero, one_mul] using
        cyclotomicClearing_mul_regular K i hbound ω hω)
  have hP' : intPolynomialMap (𝕜 := 𝕜) (X ^ m) * x =
      algebraMap 𝕜[X] (RatFunc 𝕜) P := by
    simpa [intPolynomialMap] using hP
  obtain ⟨A, hA⟩ := laurent_of_integerMonicFraction x hx m P hP'
  exact ⟨m, A, hA⟩

omit [CharZero 𝕜] in
/-- Evaluation of an integer polynomial inside the rational-function field. -/
theorem eval_intPolynomialMap_natCast (A : ℤ[X]) (p : ℕ) :
    RatFunc.eval (RingHom.id 𝕜) (p : 𝕜) (intPolynomialMap A) =
      ((A.eval (p : ℤ) : ℤ) : 𝕜) := by
  change RatFunc.eval (RingHom.id 𝕜) (p : 𝕜)
    (algebraMap 𝕜[X] (RatFunc 𝕜) (A.map (Int.castRingHom 𝕜))) = _
  rw [RatFunc.eval_algebraMap]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Polynomial.eval₂_id, Polynomial.eval_map]
  have h := Polynomial.eval₂_at_apply (p := A) (Int.castRingHom 𝕜) (p : ℤ)
  simp only [Int.coe_castRingHom, Int.cast_natCast] at h
  exact h

/-- A cleared generic integer Laurent identity gives the exact rational denominator
statement required by Proposition 4.1. -/
theorem denominators_clear_of_integer_laurent {p : ℕ} (hp : 2 ≤ p) (K i m : ℕ)
    (A : ℤ[X])
    (hA : intPolynomialMap (𝕜 := 𝕜) (X ^ m) *
      (intPolynomialMap (cyclotomicClearing K) *
        (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i) = intPolynomialMap A) :
    ((CK p K : ℚ) * (QZeta3.Delta p K).coeff i * (p : ℚ) ^ m).den = 1 := by
  let R := regularAt (p : 𝕜)
  let u : R := ⟨intPolynomialMap (𝕜 := 𝕜) (X ^ m), polynomial_mem_regularAt _ _⟩
  let v : R := ⟨intPolynomialMap (𝕜 := 𝕜) (cyclotomicClearing K),
    polynomial_mem_regularAt _ _⟩
  let w : R := ⟨(Delta (RatFunc.X : RatFunc 𝕜) K).coeff i,
    Delta_coeff_mem_regularAt_natCast hp K i⟩
  let a : R := ⟨intPolynomialMap (𝕜 := 𝕜) A, polynomial_mem_regularAt _ _⟩
  have he : u * (v * w) = a := Subtype.ext hA
  have heval := congrArg (localEval (p : 𝕜)) he
  simp only [map_mul, localEval_apply] at heval
  change RatFunc.eval (RingHom.id 𝕜) (p : 𝕜) (intPolynomialMap (X^m)) *
    (RatFunc.eval (RingHom.id 𝕜) (p : 𝕜) (intPolynomialMap (cyclotomicClearing K)) *
      RatFunc.eval (RingHom.id 𝕜) (p : 𝕜) ((Delta RatFunc.X K).coeff i)) =
    RatFunc.eval (RingHom.id 𝕜) (p : 𝕜) (intPolynomialMap A) at heval
  rw [eval_intPolynomialMap_natCast, eval_intPolynomialMap_natCast,
    eval_intPolynomialMap_natCast, eval_Delta_coeff_natCast hp K i,
    cyclotomicClearing_eval, Polynomial.eval_pow, Polynomial.eval_X] at heval
  have heq : (CK p K : ℚ) * (QZeta3.Delta p K).coeff i * (p : ℚ)^m =
      ((A.eval (p : ℤ) : ℤ) : ℚ) := by
    apply Rat.cast_injective (α := 𝕜)
    push_cast
    simpa only [Int.cast_pow, Int.cast_natCast, mul_comm, mul_left_comm, mul_assoc] using heval
  rw [heq, Rat.den_intCast]

/-- The complete arithmetic descent, parameterized only by the local cyclotomic estimate. -/
theorem denominators_clear_of_cyclotomic_bounds [IsAlgClosed 𝕜] {p : ℕ}
    (hp : 2 ≤ p) (K i : ℕ)
    (hbound : ∀ d ∈ Icc 1 K, ∀ ω : 𝕜, IsPrimitiveRoot ω d →
      uniformizer ω ^ cApp K d * (Delta (RatFunc.X : RatFunc 𝕜) K).coeff i ∈ regularAt ω) :
    ∃ m : ℕ, ((CK p K : ℚ) * (QZeta3.Delta p K).coeff i * (p : ℚ)^m).den = 1 := by
  obtain ⟨m, A, hA⟩ := exists_integer_laurent_of_cyclotomic_bounds K i hbound
  exact ⟨m, denominators_clear_of_integer_laurent hp K i m A hA⟩

end QZeta3.Generic
