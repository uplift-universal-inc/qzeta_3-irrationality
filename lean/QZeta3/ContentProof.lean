import QZeta3.Content
import QZeta3.DividedDifferences
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Arithmetic support for the content estimate

This module introduces the rational subring of numbers whose denominators are
coprime to the base. All theorems in this module are independent of the frozen
propositions. The remaining content argument must establish the translated
moment hypotheses used by the determinant lemma below.
-/

open Polynomial Finset

namespace QZeta3

variable {p : ℕ}

/-- Rational numbers integral at every prime dividing the base. -/
def baseIntegral (p : ℕ) : Subring ℚ where
  carrier := {x | Nat.Coprime x.den p}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := fun hx hy =>
    Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd _ _) (hx.mul_left hy)
  neg_mem' := by intro x hx; simpa using hx
  mul_mem' := fun hx hy =>
    Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd _ _) (hx.mul_left hy)

@[simp] theorem mem_baseIntegral (p : ℕ) (x : ℚ) :
    x ∈ baseIntegral p ↔ Nat.Coprime x.den p := Iff.rfl

/-- The denominator of a quotient of integers is a divisor of the displayed denominator. -/
theorem intCast_div_mem_baseIntegral {p : ℕ} (a b : ℤ)
    (hb : Nat.Coprime b.natAbs p) : (a : ℚ) / b ∈ baseIntegral p := by
  apply Nat.Coprime.coprime_dvd_left _ hb
  have h := Rat.den_dvd a b
  rw [← Rat.intCast_div_eq_divInt] at h
  exact_mod_cast Int.natAbs_dvd_natAbs.mpr h

/-- Each factor `p^j - 1` is a unit at primes dividing `p`. -/
theorem pow_sub_one_coprime (p j : ℕ) (hp : 1 ≤ p) (hj : 0 < j) :
    Nat.Coprime (p ^ j - 1) p := by
  have hpow : 1 ≤ p ^ j := one_le_pow₀ hp
  have hcop : Nat.Coprime (p ^ j - 1) (p ^ j) := by
    rw [Nat.coprime_self_sub_left hpow]
    exact Nat.coprime_one_left _
  exact hcop.coprime_dvd_right (dvd_pow_self p (Nat.ne_zero_of_lt hj))

/-- Every polynomial moment is integral at every prime dividing the base. -/
theorem mu_mem_baseIntegral (p j : ℕ) (hp : 1 ≤ p) : mu p j ∈ baseIntegral p := by
  by_cases hj : j = 0
  · simp [mu, hj]
  · have hpow : 1 ≤ p ^ j := one_le_pow₀ hp
    have h := intCast_div_mem_baseIntegral ((j : ℤ) ^ 2) ((p ^ j - 1 : ℕ) : ℤ)
      (by simpa using pow_sub_one_coprime p j hp (Nat.pos_of_ne_zero hj))
    simpa [mu, hj, Nat.cast_sub hpow] using h

/-- All finite pole-tail sums are integral at primes dividing the base. -/
theorem S_mem_baseIntegral (p a : ℕ) (hp : 1 ≤ p) : S p a ∈ baseIntegral p := by
  unfold S
  apply Subring.sum_mem
  intro j hj
  have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
  have hpow : 1 ≤ p ^ j := one_le_pow₀ hp
  have h := intCast_div_mem_baseIntegral
    ((p : ℤ) ^ j * ((p : ℤ) ^ j + 1)) (((p ^ j - 1 : ℕ) : ℤ) ^ 3)
    (by simpa using (pow_sub_one_coprime p j hp hjpos).pow_left 3)
  simpa [Nat.cast_sub hpow] using h

/-- A polynomial has all coefficients integral at the base precisely when it
lifts to a polynomial over the integral-at-the-base subring. -/
theorem coeff_mem_baseIntegral_iff (p : ℕ) (f : ℚ[X]) :
    (∀ i, f.coeff i ∈ baseIntegral p) ↔
      f ∈ Polynomial.liftsRing (baseIntegral p).subtype := by
  rw [← Polynomial.lifts_iff_liftsRing, Polynomial.lifts_iff_coeff_lifts]
  constructor
  · intro h i
    exact ⟨⟨f.coeff i, h i⟩, rfl⟩
  · intro h i
    obtain ⟨x, hx⟩ := h i
    exact hx ▸ x.property

/-- Determinants preserve coefficientwise integrality at the base. -/
theorem det_coeff_mem_baseIntegral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) (M : Matrix ι ι ℚ[X])
    (hM : ∀ a b i, (M a b).coeff i ∈ baseIntegral p) :
    ∀ i, M.det.coeff i ∈ baseIntegral p := by
  apply (coeff_mem_baseIntegral_iff p M.det).mpr
  let R := Polynomial.liftsRing (baseIntegral p).subtype
  have hentry : ∀ a b, M a b ∈ R := fun a b =>
    (coeff_mem_baseIntegral_iff p (M a b)).mp (hM a b)
  rw [Matrix.det_apply']
  apply R.sum_mem
  intro σ _
  apply R.mul_mem
  · exact intCast_mem R _
  · exact R.prod_mem fun i _ => hentry (σ i) i

/-- The polynomial functional preserves integrality at the base. -/
theorem Lpoly_mem_baseIntegral (p : ℕ) (hp : 1 ≤ p) (f : ℚ[X])
    (hf : ∀ i, f.coeff i ∈ baseIntegral p) : Lpoly p f ∈ baseIntegral p := by
  unfold Lpoly
  exact (baseIntegral p).sum_mem fun i _ =>
    (baseIntegral p).mul_mem (hf i) (mu_mem_baseIntegral p i hp)

/-- The pole polynomial viewed over the rational subring integral at the base. -/
noncomputable def integralF (p K : ℕ) : (baseIntegral p)[X] :=
  ∏ a ∈ Icc 1 K, (X - C (⟨(p : ℚ) ^ a,
    (baseIntegral p).pow_mem (natCast_mem (baseIntegral p) p) a⟩ : baseIntegral p))

theorem integralF_monic (p K : ℕ) : (integralF p K).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem integralF_map (p K : ℕ) :
    (integralF p K).map (baseIntegral p).subtype = F p K := by
  simp [integralF, F, Polynomial.map_prod]

/-- Dividing a monomial by the monic pole polynomial introduces no denominator
at primes dividing the base. -/
theorem quotient_coeff_mem_baseIntegral (p K k i : ℕ) :
    (X ^ k /ₘ F p K).coeff i ∈ baseIntegral p := by
  let f : (baseIntegral p)[X] := X ^ k /ₘ integralF p K
  have hmap : f.map (baseIntegral p).subtype = X ^ k /ₘ F p K := by
    rw [Polynomial.map_divByMonic _ (integralF_monic p K), integralF_map]
    simp
  rw [← hmap, Polynomial.coeff_map]
  exact (f.coeff i).property

/-- In the constant affine moment, the entire polynomial-quotient contribution
is already integral at primes dividing the base. -/
theorem quotient_moment_mem_baseIntegral (p K k : ℕ) (hp : 1 ≤ p) :
    Lpoly p (X ^ k /ₘ F p K) ∈ baseIntegral p :=
  Lpoly_mem_baseIntegral p hp _ (quotient_coeff_mem_baseIntegral p K k)

/-- Reduction modulo the monic pole polynomial preserves integral coefficients. -/
theorem remainder_coeff_mem_baseIntegral (p K : ℕ) (f : ℚ[X])
    (hf : ∀ i, f.coeff i ∈ baseIntegral p) (i : ℕ) :
    (f %ₘ F p K).coeff i ∈ baseIntegral p := by
  obtain ⟨f₀, hf₀⟩ := (Polynomial.mem_lifts f).mp
    ((Polynomial.lifts_iff_liftsRing _ _).mpr ((coeff_mem_baseIntegral_iff p f).mp hf))
  have hmap : (f₀ %ₘ integralF p K).map (baseIntegral p).subtype = f %ₘ F p K := by
    rw [Polynomial.map_modByMonic _ (integralF_monic p K), integralF_map, hf₀]
  rw [← hmap, Polynomial.coeff_map]
  exact ((f₀ %ₘ integralF p K).coeff i).property

/-- A divided difference of an integral polynomial is integral, even though its
individual barycentric summands can have denominators divisible by the base. -/
theorem residue_sum_mem_baseIntegral (hp : 2 ≤ p) (K : ℕ) (f : ℚ[X])
    (hf : ∀ i, f.coeff i ∈ baseIntegral p) :
    (∑ a ∈ Icc 1 K, f.eval ((p : ℚ) ^ a) /
      (derivative (F p K)).eval ((p : ℚ) ^ a)) ∈ baseIntegral p := by
  rw [residue_sum_Icc_eq_rem_coeff hp K f]
  exact remainder_coeff_mem_baseIntegral p K f hf _

/-- The `X` coefficient of every positive-index moment is integral at the base. -/
theorem mLin_mem_baseIntegral (hp : 2 ≤ p) (K k : ℕ) (hk : 0 < k) :
    mLin p K k ∈ baseIntegral p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hexp : ∀ a : ℕ, a * k = a * (k - 1) + a := by
    intro a
    have h : k = (k - 1) + 1 := by omega
    rw [h]
    simp only [Nat.add_sub_cancel, mul_add, mul_one]
  have hsum : mLin p K k = -(∑ a ∈ Icc 1 K,
      (X ^ (k - 1) : ℚ[X]).eval ((p : ℚ) ^ a) /
        (derivative (F p K)).eval ((p : ℚ) ^ a)) := by
    unfold mLin
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    simp only [res, Polynomial.eval_pow, Polynomial.eval_X, ← pow_mul]
    rw [hexp, pow_add, div_right_comm, mul_div_cancel_right₀ _ (pow_ne_zero a hp0)]
  rw [hsum]
  apply (baseIntegral p).neg_mem
  apply residue_sum_mem_baseIntegral hp K
  intro i
  simp only [Polynomial.coeff_X_pow]
  split_ifs <;> simp

/-- The matrix of unnormalised affine moments from Proposition 3.1. -/
noncomputable def momentMatrix (p K : ℕ) : Matrix (Fin K) (Fin K) ℚ[X] :=
  fun i j => C (mConst p K (i.val + j.val)) + C (mLin p K (i.val + j.val)) * X

/-- Normalising every entry multiplies the determinant by the `K`-th power. -/
theorem Delta_eq_momentMatrix_det (p K : ℕ) :
    Delta p K = C ((nrm p K) ^ K) * (momentMatrix p K).det := by
  have hM : (X : ℚ[X]) • (hankelLin p K).map C + (hankelConst p K).map C =
      C (nrm p K) • momentMatrix p K := by
    apply Matrix.ext
    intro i j
    change X * C (nrm p K * mLin p K (i.val + j.val)) +
      C (nrm p K * mConst p K (i.val + j.val)) =
      C (nrm p K) * (C (mConst p K (i.val + j.val)) +
        C (mLin p K (i.val + j.val)) * X)
    simp only [map_mul]
    ring
  unfold Delta
  rw [hM, Matrix.det_smul, Fintype.card_fin, ← map_pow]

/-- Scale only the first row by `p^A_K`. This is the row operation that
extracts the full content exponent in Proposition 3.1. -/
noncomputable def contentMatrix (p K : ℕ) : Matrix (Fin K) (Fin K) ℚ[X] :=
  fun i j => (if i.val = 0 then C ((p : ℚ) ^ AK K) else 1) * momentMatrix p K i j

theorem contentMatrix_det (p K : ℕ) (hK : 0 < K) :
    (contentMatrix p K).det = C ((p : ℚ) ^ AK K) * (momentMatrix p K).det := by
  unfold contentMatrix
  rw [show (fun i j : Fin K =>
      (if i.val = 0 then C ((p : ℚ) ^ AK K) else 1) * momentMatrix p K i j) =
      Matrix.of (fun i j : Fin K =>
      (if i.val = 0 then C ((p : ℚ) ^ AK K) else 1) * momentMatrix p K i j) from rfl,
    Matrix.det_mul_column]
  congr 1
  let z : Fin K := ⟨0, hK⟩
  have hzero : ∀ i : Fin K, i.val = 0 ↔ i = z := by
    intro i
    exact ⟨fun hi => Fin.ext hi, fun hi => congrArg Fin.val hi⟩
  simp_rw [hzero]
  simp

/-- The normalized determinant is a unit sign times the row-scaled determinant. -/
theorem Delta_normalized_eq_contentMatrix (hp : 2 ≤ p) (K : ℕ) (hK : 0 < K) :
    Delta p K * C (((p : ℚ) ^ eK K)⁻¹) =
      C ((-1 : ℚ) ^ (K * K)) * (contentMatrix p K).det := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hexp : AK K * K = eK K + AK K := by
    unfold eK
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hK)
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    ring
  rw [Delta_eq_momentMatrix_det, contentMatrix_det p K hK]
  have hnorm : (nrm p K) ^ K * ((p : ℚ) ^ eK K)⁻¹ =
      (-1 : ℚ) ^ (K * K) * (p : ℚ) ^ AK K := by
    unfold nrm
    rw [mul_pow, ← pow_mul, ← pow_mul, hexp, pow_add]
    field_simp
  calc C (nrm p K ^ K) * (momentMatrix p K).det * C (((p : ℚ) ^ eK K)⁻¹)
      = C ((nrm p K) ^ K * ((p : ℚ) ^ eK K)⁻¹) * (momentMatrix p K).det := by
        rw [map_mul]; ring
    _ = C ((-1 : ℚ) ^ (K * K)) *
        (C ((p : ℚ) ^ AK K) * (momentMatrix p K).det) := by
        rw [hnorm, map_mul, mul_assoc]

/-- Reduction of the content proposition to the precise row-integrality claim.
This theorem does not assert that the moment hypotheses have been discharged. -/
theorem content_coeff_of_contentMatrix (hp : 2 ≤ p) (K : ℕ) (hK : 0 < K)
    (hM : ∀ a b i, ((contentMatrix p K) a b).coeff i ∈ baseIntegral p) (i : ℕ) :
    Nat.Coprime ((Delta p K).coeff i / (p : ℚ) ^ eK K).den p := by
  have hd := det_coeff_mem_baseIntegral p (contentMatrix p K) hM i
  have hsign : (-1 : ℚ) ^ (K * K) ∈ baseIntegral p :=
    (baseIntegral p).pow_mem ((baseIntegral p).neg_mem (baseIntegral p).one_mem) _
  have h := (baseIntegral p).mul_mem hsign hd
  have heq := congrArg (fun f : ℚ[X] => f.coeff i)
    (Delta_normalized_eq_contentMatrix hp K hK)
  simp only [Polynomial.coeff_mul_C, Polynomial.coeff_C_mul] at heq
  rw [div_eq_mul_inv, heq]
  exact h

/-- The determinant of the empty Hankel matrix is the constant polynomial one. -/
@[simp] theorem Delta_zero (p : ℕ) : Delta p 0 = 1 := by simp [Delta]

/-- The size-zero case of the content assertion is unconditional. -/
theorem content_coeff_zero (p i : ℕ) :
    Nat.Coprime ((Delta p 0).coeff i / (p : ℚ) ^ eK 0).den p := by
  simp [eK, AK, Polynomial.coeff_one]
  split_ifs <;> simp

/-- The size-zero case of denominator clearing is unconditional. -/
theorem denominators_clear_zero (p i : ℕ) :
    ∃ m : ℕ, ((CK p 0 : ℚ) * (Delta p 0).coeff i * (p : ℚ) ^ m).den = 1 := by
  refine ⟨0, ?_⟩
  simp [CK, Polynomial.coeff_one]
  split_ifs <;> simp

/-- The first determinant is exactly the target variable minus its first tail. -/
theorem Delta_one_content (hp : 2 ≤ p) : Delta p 1 = X - C (S p 1) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hF : F p 1 = X - C (p : ℚ) := by simp [F]
  have hres : res p 1 0 1 = 1 := by simp [res, hF]
  have hquot : (1 : ℚ[X]) /ₘ F p 1 = 0 := by
    apply (Polynomial.divByMonic_eq_zero_iff (F_monic p 1)).mpr
    rw [hF, Polynomial.degree_one, Polynomial.degree_X_sub_C]
    norm_num
  have hconst : mConst p 1 0 = S p 1 / (p : ℚ) := by
    simp [mConst, hquot, hres, Lpoly]
  have hlin : mLin p 1 0 = -(p : ℚ)⁻¹ := by
    simp [mLin, hres]
  rw [Delta_eq_momentMatrix_det, Matrix.det_fin_one]
  have hnrm : nrm p 1 = -(p : ℚ) := by norm_num [nrm, AK]
  rw [hnrm, pow_one]
  simp only [momentMatrix, Fin.val_zero, zero_add, hconst, hlin]
  have h₁ : -(p : ℚ) * (S p 1 / (p : ℚ)) = -S p 1 := by field_simp
  have h₂ : -(p : ℚ) * -(p : ℚ)⁻¹ = 1 := by field_simp
  rw [mul_add, ← mul_assoc, ← map_mul, ← map_mul, h₁, h₂, map_one, one_mul, map_neg]
  ring

/-- The size-one content claim follows from the explicit affine determinant. -/
theorem content_coeff_one (hp : 2 ≤ p) (i : ℕ) :
    Nat.Coprime ((Delta p 1).coeff i / (p : ℚ) ^ eK 1).den p := by
  have hmem : X - C (S p 1) ∈ Polynomial.liftsRing (baseIntegral p).subtype := by
    apply Subring.sub_mem
    · exact (Polynomial.lifts_iff_liftsRing _ _).mp
        (Polynomial.X_mem_lifts (baseIntegral p).subtype)
    · exact (Polynomial.lifts_iff_liftsRing _ _).mp
        (Polynomial.C'_mem_lifts ⟨⟨S p 1, S_mem_baseIntegral p 1 (by omega)⟩, rfl⟩)
  have h := (coeff_mem_baseIntegral_iff p _).mpr hmem i
  simpa [Delta_one_content hp, eK, AK] using h

@[simp] theorem CK_one (p : ℕ) : CK p 1 = ((p : ℤ) - 1) ^ 3 := by
  simp [CK, Phi, cApp, Polynomial.cyclotomic_one]

/-- The size-one clearing multiplier cancels the cubic pole exactly. -/
theorem denominators_clear_one (hp : 2 ≤ p) (i : ℕ) :
    ∃ m : ℕ, ((CK p 1 : ℚ) * (Delta p 1).coeff i * (p : ℚ) ^ m).den = 1 := by
  refine ⟨0, ?_⟩
  rw [pow_zero, mul_one, CK_one, Delta_one_content hp]
  have hp1 : (p : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ p := by exact_mod_cast hp
    linarith
  have hS : S p 1 = (p : ℚ) * ((p : ℚ) + 1) / ((p : ℚ) - 1) ^ 3 := by simp [S]
  by_cases hi0 : i = 0
  · subst i
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
      zero_sub, hS]
    have heq : ((((p : ℤ) - 1) ^ 3 : ℤ) : ℚ) *
        -((p : ℚ) * ((p : ℚ) + 1) / ((p : ℚ) - 1) ^ 3) =
        ((-(p : ℤ) * ((p : ℤ) + 1) : ℤ) : ℚ) := by
      push_cast
      field_simp
    rw [heq]
    exact Rat.den_intCast _
  · by_cases hi1 : i = 1
    · subst i
      simp [Polynomial.coeff_sub, Polynomial.coeff_X]
    · simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C, hi0,
        Ne.symm hi1]

end QZeta3
