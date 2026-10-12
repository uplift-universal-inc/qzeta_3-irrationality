import QZeta3.Defs
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.LinearAlgebra.Lagrange

/-!
# Generic moving-denominator moments and their algebraic localization

The scalar base is an arbitrary element of a field. This permits later use of
an indeterminate and cyclotomic local rings, while specialization to natural
bases is definitionally the original construction.
-/

open Polynomial Finset

namespace QZeta3.Generic

variable {𝕜 : Type*} [Field 𝕜]

def mu (z : 𝕜) (j : ℕ) : 𝕜 := if j = 0 then 0 else (j : 𝕜) ^ 2 / (z ^ j - 1)
def S (z : 𝕜) (a : ℕ) : 𝕜 := ∑ b ∈ Icc 1 a, z ^ b * (z ^ b + 1) / (z ^ b - 1) ^ 3
noncomputable def F (z : 𝕜) (K : ℕ) : 𝕜[X] := ∏ a ∈ Icc 1 K, (X - C (z ^ a))
noncomputable def Lpoly (z : 𝕜) (f : 𝕜[X]) : 𝕜 := ∑ j ∈ f.support, f.coeff j * mu z j
noncomputable def res (z : 𝕜) (K k a : ℕ) : 𝕜 := z ^ (a*k) / (derivative (F z K)).eval (z ^ a)
noncomputable def mConst (z : 𝕜) (K k : ℕ) : 𝕜 :=
  Lpoly z (X ^ k /ₘ F z K) + ∑ a ∈ Icc 1 K, res z K k a * S z a / z ^ a
noncomputable def mLin (z : 𝕜) (K k : ℕ) : 𝕜 := -∑ a ∈ Icc 1 K, res z K k a / z ^ a
def nrm (z : 𝕜) (K : ℕ) : 𝕜 := (-1) ^ K * z ^ AK K
noncomputable def hankelLin (z : 𝕜) (K : ℕ) : Matrix (Fin K) (Fin K) 𝕜 :=
  Matrix.of fun i j => nrm z K * mLin z K (i.val+j.val)
noncomputable def hankelConst (z : 𝕜) (K : ℕ) : Matrix (Fin K) (Fin K) 𝕜 :=
  Matrix.of fun i j => nrm z K * mConst z K (i.val+j.val)
noncomputable def Delta (z : 𝕜) (K : ℕ) : 𝕜[X] :=
  Matrix.det ((X : 𝕜[X]) • (hankelLin z K).map C + (hankelConst z K).map C)

/-- Specialization at a natural rational base is exactly the original determinant. -/
theorem Delta_natCast (p K : ℕ) : Delta (p : ℚ) K = QZeta3.Delta p K := rfl

theorem F_monic (z : 𝕜) (K : ℕ) : (F z K).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem F_natDegree (z : 𝕜) (K : ℕ) : (F z K).natDegree = K := by
  unfold F
  rw [Polynomial.natDegree_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _,
    Finset.sum_congr rfl fun _ _ => Polynomial.natDegree_X_sub_C _]
  simp

/-- At a labeled root, the derivative is the product of the other root differences.
The identity remains valid if other roots happen to coincide. -/
theorem derivative_F_eval_eq_prod (z : 𝕜) (K a : ℕ) (ha : a ∈ Icc 1 K) :
    (derivative (F z K)).eval (z ^ a) = ∏ b ∈ (Icc 1 K).erase a, (z ^ a - z ^ b) := by
  have hF : F z K = (X - C (z ^ a)) * ∏ b ∈ (Icc 1 K).erase a, (X - C (z ^ b)) := by
    exact (Finset.mul_prod_erase _ _ ha).symm
  rw [hF, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_C]
  simp [Polynomial.eval_prod]

/-- Coefficientwise membership is equivalent to lifting the polynomial to a subring. -/
theorem coeff_mem_iff_lifts (R : Subring 𝕜) (f : 𝕜[X]) :
    (∀ i, f.coeff i ∈ R) ↔ f ∈ Polynomial.liftsRing R.subtype := by
  rw [← Polynomial.lifts_iff_liftsRing, Polynomial.lifts_iff_coeff_lifts]
  constructor
  · intro h i
    exact ⟨⟨f.coeff i, h i⟩, rfl⟩
  · intro h i
    obtain ⟨x, hx⟩ := h i
    exact hx ▸ x.property

theorem det_coeff_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Subring 𝕜) (M : Matrix ι ι 𝕜[X])
    (hM : ∀ a b i, (M a b).coeff i ∈ R) : ∀ i, M.det.coeff i ∈ R := by
  apply (coeff_mem_iff_lifts R M.det).mpr
  let T := Polynomial.liftsRing R.subtype
  have hentry : ∀ a b, M a b ∈ T := fun a b => (coeff_mem_iff_lifts R _).mp (hM a b)
  rw [Matrix.det_apply']
  apply T.sum_mem
  intro σ _
  exact T.mul_mem (intCast_mem T _) (T.prod_mem fun i _ => hentry (σ i) i)

/-- A pole polynomial can be formed over any subring containing the base. -/
noncomputable def subringF (R : Subring 𝕜) (z : 𝕜) (hz : z ∈ R) (K : ℕ) : R[X] :=
  ∏ a ∈ Icc 1 K, (X - C (⟨z ^ a, R.pow_mem hz a⟩ : R))

theorem subringF_monic (R : Subring 𝕜) (z : 𝕜) (hz : z ∈ R) (K : ℕ) :
    (subringF R z hz K).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem subringF_map (R : Subring 𝕜) (z : 𝕜) (hz : z ∈ R) (K : ℕ) :
    (subringF R z hz K).map R.subtype = F z K := by
  simp [subringF, F, Polynomial.map_prod]

/-- Monic division by the pole polynomial preserves membership of every coefficient. -/
theorem quotient_coeff_mem_subring (R : Subring 𝕜) (z : 𝕜) (hz : z ∈ R) (K : ℕ)
    (f : 𝕜[X]) (hf : ∀ i, f.coeff i ∈ R) (i : ℕ) : (f /ₘ F z K).coeff i ∈ R := by
  obtain ⟨f₀, hf₀⟩ := (Polynomial.mem_lifts f).mp
    ((Polynomial.lifts_iff_liftsRing _ _).mpr ((coeff_mem_iff_lifts R f).mp hf))
  have hmap : (f₀ /ₘ subringF R z hz K).map R.subtype = f /ₘ F z K := by
    rw [Polynomial.map_divByMonic _ (subringF_monic R z hz K), subringF_map, hf₀]
  rw [← hmap, Polynomial.coeff_map]
  exact ((f₀ /ₘ subringF R z hz K).coeff i).property

/-- The concrete localization assumptions needed by the construction. -/
structure LocalizationData (R : Subring 𝕜) (z : 𝕜) (K : ℕ) : Prop where
  base_mem : z ∈ R
  inv_base_mem : z⁻¹ ∈ R
  inv_geom_mem : ∀ n ∈ Icc 1 K, (z ^ n - 1)⁻¹ ∈ R

namespace LocalizationData

variable {R : Subring 𝕜} {z : 𝕜} {K : ℕ} (h : LocalizationData R z K)

include h

theorem inv_difference_mem (a b : ℕ) (ha : a ≤ K) (hb : b ≤ K) (hab : a ≠ b) :
    (z ^ a - z ^ b)⁻¹ ∈ R := by
  by_cases hlt : a < b
  · have hgeom := h.inv_geom_mem (b-a) (mem_Icc.mpr ⟨by omega, by omega⟩)
    have heq : z ^ a - z ^ b = -(z ^ a * (z ^ (b-a) - 1)) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_of_le hlt.le]
      ring
    rw [heq, inv_neg, mul_inv, ← inv_pow]
    exact R.neg_mem (R.mul_mem (R.pow_mem h.inv_base_mem a) hgeom)
  · have hgeom := h.inv_geom_mem (a-b) (mem_Icc.mpr ⟨by omega, by omega⟩)
    have heq : z ^ a - z ^ b = z ^ b * (z ^ (a-b) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_of_le (by omega : b ≤ a)]
      ring
    rw [heq, mul_inv, ← inv_pow]
    exact R.mul_mem (R.pow_mem h.inv_base_mem b) hgeom

theorem inverse_derivative_mem (a : ℕ) (ha : a ∈ Icc 1 K) :
    ((derivative (F z K)).eval (z ^ a))⁻¹ ∈ R := by
  rw [derivative_F_eval_eq_prod z K a ha, ← Finset.prod_inv_distrib]
  exact R.prod_mem fun b hb => h.inv_difference_mem a b (mem_Icc.mp ha).2
    (mem_Icc.mp (mem_erase.mp hb).2).2 (mem_erase.mp hb).1.symm

theorem res_mem (k a : ℕ) (ha : a ∈ Icc 1 K) : res z K k a ∈ R := by
  rw [res, div_eq_mul_inv]
  exact R.mul_mem (R.pow_mem h.base_mem _) (h.inverse_derivative_mem a ha)

theorem S_mem (a : ℕ) (ha : a ≤ K) : S z a ∈ R := by
  unfold S
  apply R.sum_mem
  intro b hb
  rw [div_eq_mul_inv, ← inv_pow]
  exact R.mul_mem (R.mul_mem (R.pow_mem h.base_mem _)
    (R.add_mem (R.pow_mem h.base_mem _) R.one_mem))
    (R.pow_mem (h.inv_geom_mem b (mem_Icc.mpr ⟨(mem_Icc.mp hb).1,
      (mem_Icc.mp hb).2.trans ha⟩)) _)

theorem mu_mem (j : ℕ) (hj : j ≤ K) : mu z j ∈ R := by
  unfold mu
  split_ifs with hzero
  · exact R.zero_mem
  · rw [div_eq_mul_inv]
    exact R.mul_mem (R.pow_mem (natCast_mem R j) 2)
      (h.inv_geom_mem j (mem_Icc.mpr ⟨by omega, hj⟩))

theorem mLin_mem (k : ℕ) : mLin z K k ∈ R := by
  unfold mLin
  apply R.neg_mem
  apply R.sum_mem
  intro a ha
  rw [div_eq_mul_inv, ← inv_pow]
  exact R.mul_mem (h.res_mem k a ha) (R.pow_mem h.inv_base_mem a)

/-- Lift the monic pole polynomial into the chosen localization ring. -/
noncomputable def integralF : R[X] :=
  ∏ a ∈ Icc 1 K, (X - C (⟨z ^ a, R.pow_mem h.base_mem a⟩ : R))

theorem integralF_monic : (h.integralF).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem integralF_map : (h.integralF).map R.subtype = F z K := by
  simp [integralF, F, Polynomial.map_prod]

theorem quotient_coeff_mem (k i : ℕ) : (X ^ k /ₘ F z K).coeff i ∈ R := by
  let f : R[X] := X ^ k /ₘ h.integralF
  have hmap : f.map R.subtype = X ^ k /ₘ F z K := by
    rw [Polynomial.map_divByMonic _ h.integralF_monic, h.integralF_map]
    simp
  rw [← hmap, Polynomial.coeff_map]
  exact (f.coeff i).property

theorem Lpoly_mem (f : 𝕜[X]) (hf : ∀ i, f.coeff i ∈ R) (hdeg : f.natDegree ≤ K) :
    Lpoly z f ∈ R := by
  unfold Lpoly
  apply R.sum_mem
  intro i hi
  exact R.mul_mem (hf i) (h.mu_mem i
    ((Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi)).trans hdeg))

theorem quotient_moment_mem (k : ℕ) (hk : k ≤ 2*K) : Lpoly z (X ^ k /ₘ F z K) ∈ R := by
  apply h.Lpoly_mem _ (h.quotient_coeff_mem k)
  rw [Polynomial.natDegree_divByMonic _ (F_monic z K), Polynomial.natDegree_X_pow, F_natDegree]
  omega

theorem mConst_mem (k : ℕ) (hk : k ≤ 2*K) : mConst z K k ∈ R := by
  unfold mConst
  apply R.add_mem (h.quotient_moment_mem k hk)
  apply R.sum_mem
  intro a ha
  rw [div_eq_mul_inv, ← inv_pow]
  exact R.mul_mem (R.mul_mem (h.res_mem k a ha) (h.S_mem a (mem_Icc.mp ha).2))
    (R.pow_mem h.inv_base_mem a)

theorem nrm_mem : nrm z K ∈ R :=
  R.mul_mem (R.pow_mem (R.neg_mem R.one_mem) K) (R.pow_mem h.base_mem (AK K))

/-- The complete original coefficient localization: no denominators beyond powers
of the base and the geometric factors `z^n−1`, `1≤n≤K`, occur. -/
theorem Delta_coeff_mem (i : ℕ) : (Delta z K).coeff i ∈ R := by
  unfold Delta
  apply det_coeff_mem R
  intro a b j
  let T := Polynomial.liftsRing R.subtype
  have hC (x : 𝕜) (hx : x ∈ R) : C x ∈ T :=
    (Polynomial.lifts_iff_liftsRing _ _).mp
      (Polynomial.C'_mem_lifts ⟨⟨x, hx⟩, rfl⟩)
  have hX : (X : 𝕜[X]) ∈ T :=
    (Polynomial.lifts_iff_liftsRing _ _).mp (Polynomial.X_mem_lifts R.subtype)
  have hp := T.add_mem (T.mul_mem hX
      (hC (nrm z K * mLin z K (a.val+b.val)) (R.mul_mem h.nrm_mem (h.mLin_mem _))))
    (hC (nrm z K * mConst z K (a.val+b.val))
      (R.mul_mem h.nrm_mem (h.mConst_mem _ (by have := a.isLt; have := b.isLt; omega))))
  exact (coeff_mem_iff_lifts R _).mpr hp j

end LocalizationData
end QZeta3.Generic
