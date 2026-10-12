import QZeta3.GenericMoments
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Rational functions regular at a root of unity

The local ring is described by explicit polynomial fractions whose denominator
does not vanish. Pole clearing is stated as membership after multiplication by
a power of the uniformizer, avoiding completion or square-root parameters.
-/

open Polynomial

namespace QZeta3.Generic

variable {𝕜 : Type*} [Field 𝕜]

/-- A rational function is regular at `ω` if it has a polynomial fraction
presentation with denominator nonzero at `ω`. -/
def RegularAt (ω : 𝕜) (x : RatFunc 𝕜) : Prop :=
  ∃ f g : 𝕜[X], g.eval ω ≠ 0 ∧ x = algebraMap 𝕜[X] (RatFunc 𝕜) f /
    algebraMap 𝕜[X] (RatFunc 𝕜) g

private theorem map_ne_zero_of_eval_ne_zero (ω : 𝕜) (g : 𝕜[X]) (hg : g.eval ω ≠ 0) :
    algebraMap 𝕜[X] (RatFunc 𝕜) g ≠ 0 := by
  apply RatFunc.algebraMap_ne_zero
  intro heq
  exact hg (by rw [heq, Polynomial.eval_zero])

/-- The local subring of rational functions regular at `ω`. -/
def regularAt (ω : 𝕜) : Subring (RatFunc 𝕜) where
  carrier := {x | RegularAt ω x}
  zero_mem' := ⟨0, 1, by simp, by simp⟩
  one_mem' := ⟨1, 1, by simp, by simp⟩
  neg_mem' := by
    rintro x ⟨f, g, hg, rfl⟩
    exact ⟨-f, g, hg, by rw [map_neg, neg_div]⟩
  add_mem' := by
    rintro x y ⟨f, g, hg, rfl⟩ ⟨u, v, hv, rfl⟩
    refine ⟨f*v+u*g, g*v, ?_, ?_⟩
    · simpa only [Polynomial.eval_mul] using mul_ne_zero hg hv
    · rw [map_add, map_mul, map_mul, map_mul]
      have hg0 := map_ne_zero_of_eval_ne_zero ω g hg
      have hv0 := map_ne_zero_of_eval_ne_zero ω v hv
      field_simp
  mul_mem' := by
    rintro x y ⟨f, g, hg, rfl⟩ ⟨u, v, hv, rfl⟩
    refine ⟨f*u, g*v, ?_, ?_⟩
    · simpa only [Polynomial.eval_mul] using mul_ne_zero hg hv
    · rw [map_mul, map_mul, div_mul_div_comm]

@[simp] theorem mem_regularAt (ω : 𝕜) (x : RatFunc 𝕜) :
    x ∈ regularAt ω ↔ RegularAt ω x := Iff.rfl

theorem polynomial_mem_regularAt (ω : 𝕜) (f : 𝕜[X]) :
    algebraMap 𝕜[X] (RatFunc 𝕜) f ∈ regularAt ω := ⟨f, 1, by simp, by simp⟩

theorem inv_polynomial_mem_regularAt (ω : 𝕜) (f : 𝕜[X]) (hf : f.eval ω ≠ 0) :
    (algebraMap 𝕜[X] (RatFunc 𝕜) f)⁻¹ ∈ regularAt ω :=
  ⟨1, f, hf, by simp⟩

/-- The local uniformizer `z−ω`. -/
noncomputable def uniformizer (ω : 𝕜) : RatFunc 𝕜 :=
  algebraMap 𝕜[X] (RatFunc 𝕜) (X-C ω)

theorem uniformizer_mem (ω : 𝕜) : uniformizer ω ∈ regularAt ω :=
  polynomial_mem_regularAt ω _

theorem uniformizer_ne_zero (ω : 𝕜) : uniformizer ω ≠ 0 := by
  apply RatFunc.algebraMap_ne_zero
  exact Polynomial.X_sub_C_ne_zero ω

/-- A simple zero cancels with one uniformizer factor. -/
theorem uniformizer_div_mem_of_simple_root (ω : 𝕜) (f : 𝕜[X])
    (hf : f.eval ω = 0) (hder : (derivative f).eval ω ≠ 0) :
    uniformizer ω / algebraMap 𝕜[X] (RatFunc 𝕜) f ∈ regularAt ω := by
  let q := f /ₘ (X-C ω)
  have hq : f = (X-C ω)*q := by
    exact ((Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hf).symm
  have hqe : q.eval ω ≠ 0 := by
    rw [hq, Polynomial.derivative_mul, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_C] at hder
    simpa using hder
  have hu := uniformizer_ne_zero ω
  rw [hq, map_mul]
  change uniformizer ω / (uniformizer ω * algebraMap 𝕜[X] (RatFunc 𝕜) q) ∈ regularAt ω
  rw [div_mul_eq_div_mul_one_div, div_self hu, one_mul]
  simpa only [one_div] using inv_polynomial_mem_regularAt ω q hqe

@[simp] theorem uniformizer_eq (ω : 𝕜) : uniformizer ω = RatFunc.X - RatFunc.C ω := by
  simp [uniformizer, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem base_mem_regularAt (ω : 𝕜) : (RatFunc.X : RatFunc 𝕜) ∈ regularAt ω :=
  polynomial_mem_regularAt ω X

theorem inv_base_mem_regularAt (ω : 𝕜) (hω : ω ≠ 0) :
    (RatFunc.X : RatFunc 𝕜)⁻¹ ∈ regularAt ω :=
  inv_polynomial_mem_regularAt ω X (by simpa using hω)

theorem inv_geometric_mem_regularAt (ω : 𝕜) (n : ℕ) (hn : ω ^ n ≠ 1) :
    ((RatFunc.X : RatFunc 𝕜) ^ n - 1)⁻¹ ∈ regularAt ω := by
  have h := inv_polynomial_mem_regularAt ω (X ^ n - 1)
    (by simpa using sub_ne_zero.mpr hn)
  simpa only [map_sub, map_pow, RatFunc.algebraMap_X, map_one] using h

theorem inv_difference_mem_regularAt (ω : 𝕜) (a b : ℕ) (hab : ω ^ a ≠ ω ^ b) :
    ((RatFunc.X : RatFunc 𝕜) ^ a - RatFunc.X ^ b)⁻¹ ∈ regularAt ω := by
  have h := inv_polynomial_mem_regularAt ω (X ^ a - X ^ b)
    (by simpa using sub_ne_zero.mpr hab)
  simpa only [map_sub, map_pow, RatFunc.algebraMap_X] using h

/-- Every nonconstant geometric factor has at most a simple zero away from zero. -/
theorem uniformizer_div_geometric_mem [CharZero 𝕜] (ω : 𝕜) (hω : ω ≠ 0)
    (n : ℕ) (hn : 0 < n) :
    uniformizer ω / ((RatFunc.X : RatFunc 𝕜) ^ n - 1) ∈ regularAt ω := by
  by_cases hroot : ω ^ n = 1
  · have hder : (derivative (X ^ n - 1 : 𝕜[X])).eval ω ≠ 0 := by
      simp only [Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero,
        Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hn)) (pow_ne_zero _ hω)
    have h := uniformizer_div_mem_of_simple_root ω (X ^ n - 1)
      (by simp [hroot]) hder
    simpa only [map_sub, map_pow, RatFunc.algebraMap_X, map_one] using h
  · rw [div_eq_mul_inv]
    exact (regularAt ω).mul_mem (uniformizer_mem ω) (inv_geometric_mem_regularAt ω n hroot)

/-- Two distinct geometric nodes have at most a simple collision at a nonzero point. -/
theorem uniformizer_div_difference_mem [CharZero 𝕜] (ω : 𝕜) (hω : ω ≠ 0)
    (a b : ℕ) (hab : a ≠ b) :
    uniformizer ω / ((RatFunc.X : RatFunc 𝕜) ^ a - RatFunc.X ^ b) ∈ regularAt ω := by
  let z : RatFunc 𝕜 := RatFunc.X
  have hzInv : z⁻¹ ∈ regularAt ω := inv_base_mem_regularAt ω hω
  by_cases hlt : a < b
  · have hg := uniformizer_div_geometric_mem ω hω (b-a) (by omega)
    have heq : z ^ a - z ^ b = -(z ^ a * (z ^ (b-a) - 1)) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_of_le hlt.le]
      ring
    change uniformizer ω / (z ^ a - z ^ b) ∈ regularAt ω
    rw [heq]
    have h := (regularAt ω).neg_mem ((regularAt ω).mul_mem
      ((regularAt ω).pow_mem hzInv a) hg)
    convert h using 1
    simp only [div_eq_mul_inv, inv_neg, mul_inv, inv_pow]
    ring
  · have hg := uniformizer_div_geometric_mem ω hω (a-b) (by omega)
    have heq : z ^ a - z ^ b = z ^ b * (z ^ (a-b) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_of_le (by omega : b ≤ a)]
      ring
    change uniformizer ω / (z ^ a - z ^ b) ∈ regularAt ω
    rw [heq]
    have h := (regularAt ω).mul_mem ((regularAt ω).pow_mem hzInv b) hg
    convert h using 1
    simp only [div_eq_mul_inv, mul_inv, inv_pow]
    ring

/-- A vanishing polynomial has a regular quotient by the uniformizer. -/
theorem polynomial_div_uniformizer_mem (ω : 𝕜) (f : 𝕜[X]) (hf : f.eval ω = 0) :
    algebraMap 𝕜[X] (RatFunc 𝕜) f / uniformizer ω ∈ regularAt ω := by
  have hq : f = (X-C ω) * (f /ₘ (X-C ω)) :=
    ((Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hf).symm
  rw [hq, map_mul]
  change uniformizer ω * algebraMap 𝕜[X] (RatFunc 𝕜) (f /ₘ (X-C ω)) / uniformizer ω ∈ regularAt ω
  rw [mul_div_cancel_left₀ _ (uniformizer_ne_zero ω)]
  exact polynomial_mem_regularAt ω _

theorem difference_div_uniformizer_mem (ω : 𝕜) (a b : ℕ) (hab : ω ^ a = ω ^ b) :
    ((RatFunc.X : RatFunc 𝕜) ^ a - RatFunc.X ^ b) / uniformizer ω ∈ regularAt ω := by
  have h := polynomial_div_uniformizer_mem ω (X ^ a - X ^ b) (by simp [hab])
  simpa only [map_sub, map_pow, RatFunc.algebraMap_X] using h

theorem pow_sub_const_div_uniformizer_mem (ω : 𝕜) (a : ℕ) :
    ((RatFunc.X : RatFunc 𝕜) ^ a - RatFunc.C (ω ^ a)) / uniformizer ω ∈ regularAt ω := by
  have h := polynomial_div_uniformizer_mem ω (X ^ a - C (ω ^ a)) (by simp)
  simpa only [map_sub, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using h

/-- Every polynomial moment has at most a simple pole at a nonzero point. -/
theorem uniformizer_mul_mu_mem [CharZero 𝕜] (ω : 𝕜) (hω : ω ≠ 0) (j : ℕ) :
    uniformizer ω * mu (RatFunc.X : RatFunc 𝕜) j ∈ regularAt ω := by
  by_cases hj : j = 0
  · simp [mu, hj]
  have h := (regularAt ω).mul_mem ((regularAt ω).pow_mem (natCast_mem (regularAt ω) j) 2)
    (uniformizer_div_geometric_mem ω hω j (Nat.pos_of_ne_zero hj))
  unfold mu
  rw [ite_eq_right hj]
  convert h using 1
  ring

/-- Every finite pole-tail has at most a third-order pole at a nonzero point. -/
theorem uniformizer_cube_mul_S_mem [CharZero 𝕜] (ω : 𝕜) (hω : ω ≠ 0) (a : ℕ) :
    uniformizer ω ^ 3 * S (RatFunc.X : RatFunc 𝕜) a ∈ regularAt ω := by
  unfold S
  rw [Finset.mul_sum]
  apply (regularAt ω).sum_mem
  intro b hb
  have h := (regularAt ω).mul_mem
    ((regularAt ω).mul_mem ((regularAt ω).pow_mem (base_mem_regularAt ω) b)
      ((regularAt ω).add_mem ((regularAt ω).pow_mem (base_mem_regularAt ω) b)
        (regularAt ω).one_mem))
    ((regularAt ω).pow_mem (uniformizer_div_geometric_mem ω hω b (Finset.mem_Icc.mp hb).1) 3)
  convert h using 1
  rw [div_pow]
  ring

/-- A pole-tail is regular if none of its geometric denominators vanishes. -/
theorem S_mem_regularAt_of_pow_ne_one (ω : 𝕜) (a : ℕ)
    (h : ∀ b ∈ Finset.Icc 1 a, ω ^ b ≠ 1) :
    S (RatFunc.X : RatFunc 𝕜) a ∈ regularAt ω := by
  unfold S
  apply (regularAt ω).sum_mem
  intro b hb
  rw [div_eq_mul_inv, ← inv_pow]
  exact (regularAt ω).mul_mem
    ((regularAt ω).mul_mem ((regularAt ω).pow_mem (base_mem_regularAt ω) b)
      ((regularAt ω).add_mem ((regularAt ω).pow_mem (base_mem_regularAt ω) b)
        (regularAt ω).one_mem))
    ((regularAt ω).pow_mem (inv_geometric_mem_regularAt ω b (h b hb)) 3)

/-- Number of other labeled nodes colliding with node `a` at the chosen local point. -/
noncomputable def collisionCount (ω : 𝕜) (K a : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 K).erase a |>.filter fun b => ω ^ a = ω ^ b).card

/-- Exactly the colliding-node factors are needed to clear a pole derivative. -/
theorem uniformizer_pow_div_derivative_mem [CharZero 𝕜] (ω : 𝕜) (hω : ω ≠ 0)
    (K a : ℕ) (ha : a ∈ Finset.Icc 1 K) :
    uniformizer ω ^ collisionCount ω K a /
      (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X ^ a) ∈ regularAt ω := by
  classical
  have hprod : (∏ b ∈ (Finset.Icc 1 K).erase a,
      (if ω ^ a = ω ^ b then uniformizer ω else 1) /
        ((RatFunc.X : RatFunc 𝕜) ^ a - RatFunc.X ^ b)) ∈ regularAt ω := by
    apply (regularAt ω).prod_mem
    intro b hb
    by_cases hab : ω ^ a = ω ^ b
    · rw [ite_eq_left hab]
      exact uniformizer_div_difference_mem ω hω a b (Finset.mem_erase.mp hb).1.symm
    · rw [ite_eq_right hab, one_div]
      exact inv_difference_mem_regularAt ω a b hab
  rw [Finset.prod_div_distrib] at hprod
  have hnum : (∏ b ∈ (Finset.Icc 1 K).erase a,
      if ω ^ a = ω ^ b then uniformizer ω else 1) =
      uniformizer ω ^ collisionCount ω K a := by
    rw [← Finset.prod_filter]
    simp [collisionCount]
  rw [hnum, ← derivative_F_eval_eq_prod RatFunc.X K a ha] at hprod
  exact hprod

/-- Clearing the colliding-node factors makes every normalized residue regular. -/
theorem uniformizer_pow_mul_residue_mem [CharZero 𝕜] (ω : 𝕜) (hω : ω ≠ 0)
    (K k a : ℕ) (ha : a ∈ Finset.Icc 1 K) :
    uniformizer ω ^ collisionCount ω K a *
      (res (RatFunc.X : RatFunc 𝕜) K k a / RatFunc.X ^ a) ∈ regularAt ω := by
  have h := (regularAt ω).mul_mem
    ((regularAt ω).mul_mem (uniformizer_pow_div_derivative_mem ω hω K a ha)
      ((regularAt ω).pow_mem (base_mem_regularAt ω) (a*k)))
    ((regularAt ω).pow_mem (inv_base_mem_regularAt ω hω) a)
  convert h using 1
  simp only [res, div_eq_mul_inv, inv_pow]
  ring

/-- If a polynomial has regular coefficients, applying the polynomial moment
functional introduces at most one simple pole. -/
theorem uniformizer_mul_Lpoly_mem [CharZero 𝕜] (ω : 𝕜) (hω : ω ≠ 0)
    (f : (RatFunc 𝕜)[X]) (hf : ∀ i, f.coeff i ∈ regularAt ω) :
    uniformizer ω * Lpoly (RatFunc.X : RatFunc 𝕜) f ∈ regularAt ω := by
  unfold Lpoly
  rw [Finset.mul_sum]
  apply (regularAt ω).sum_mem
  intro j _
  have h := (regularAt ω).mul_mem (hf j) (uniformizer_mul_mu_mem ω hω j)
  convert h using 1
  ring

/-- The polynomial quotient contribution to a Gram entry has at most a simple pole. -/
theorem uniformizer_mul_quotient_moment_mem [CharZero 𝕜] (ω : 𝕜) (hω : ω ≠ 0)
    (K : ℕ) (f : (RatFunc 𝕜)[X]) (hf : ∀ i, f.coeff i ∈ regularAt ω) :
    uniformizer ω * Lpoly (RatFunc.X : RatFunc 𝕜) (f /ₘ F RatFunc.X K) ∈ regularAt ω :=
  uniformizer_mul_Lpoly_mem ω hω _
    (quotient_coeff_mem_subring (regularAt ω) RatFunc.X (base_mem_regularAt ω) K f hf)

/-- Away from its own geometric zeros, a polynomial moment is regular. -/
theorem mu_mem_regularAt_of_pow_ne_one (ω : 𝕜) (j : ℕ) (hj : ω ^ j ≠ 1) :
    mu (RatFunc.X : RatFunc 𝕜) j ∈ regularAt ω := by
  unfold mu
  split_ifs
  · exact (regularAt ω).zero_mem
  · rw [div_eq_mul_inv]
    exact (regularAt ω).mul_mem ((regularAt ω).pow_mem (natCast_mem (regularAt ω) j) 2)
      (inv_geometric_mem_regularAt ω j hj)

/-- Polynomial evaluation preserves local regularity. -/
theorem eval_mem_regularAt (ω : 𝕜) (f : (RatFunc 𝕜)[X])
    (hf : ∀ i, f.coeff i ∈ regularAt ω) (x : RatFunc 𝕜) (hx : x ∈ regularAt ω) :
    f.eval x ∈ regularAt ω := by
  rw [Polynomial.eval_eq_sum_range]
  exact (regularAt ω).sum_mem fun i _ =>
    (regularAt ω).mul_mem (hf i) ((regularAt ω).pow_mem hx i)

/-- Vanishing cluster-basis factors give their expected uniformizer powers at a node. -/
theorem cluster_numerator_eval_div_mem (ω : 𝕜) (α : 𝕜) (a j : ℕ)
    (ha : ω ^ a = α) (V : (RatFunc 𝕜)[X]) (hV : ∀ i, V.coeff i ∈ regularAt ω) :
    ((V * (X-C (RatFunc.C α)) ^ j).eval (RatFunc.X ^ a)) / uniformizer ω ^ j ∈ regularAt ω := by
  have hv := eval_mem_regularAt ω V hV (RatFunc.X ^ a)
    ((regularAt ω).pow_mem (base_mem_regularAt ω) a)
  have hd := pow_sub_const_div_uniformizer_mem ω a
  rw [ha] at hd
  have h := (regularAt ω).mul_mem hv ((regularAt ω).pow_mem hd j)
  convert h using 1
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, div_pow]
  ring

/-- General pole bookkeeping in the local ring: a zero of order `v` cancels
`v` of the denominator's `c` possible pole factors. -/
theorem scaled_ratio_mem (ω : 𝕜) (N D : RatFunc 𝕜) (v c w : ℕ)
    (hN : N / uniformizer ω ^ v ∈ regularAt ω)
    (hD : uniformizer ω ^ c / D ∈ regularAt ω) (hc : c ≤ w+v) :
    uniformizer ω ^ w * (N/D) ∈ regularAt ω := by
  have h := (regularAt ω).mul_mem ((regularAt ω).mul_mem hN hD)
    ((regularAt ω).pow_mem (uniformizer_mem ω) (w+v-c))
  have he : c + (w+v-c) = w+v := Nat.add_sub_of_le hc
  convert h using 1
  simp only [div_eq_mul_inv]
  have ht : uniformizer ω ^ v ≠ 0 := pow_ne_zero _ (uniformizer_ne_zero ω)
  apply (mul_right_inj' ht).mp
  rw [mul_assoc, mul_assoc]
  field_simp
  have hp : uniformizer ω ^ c * uniformizer ω ^ (w+v-c) = uniformizer ω ^ (w+v) := by
    rw [← pow_add, he]
  rw [mul_assoc N, hp, pow_add]
  ring

/-- Two numerator factors can be combined without losing their zero orders. -/
theorem product_div_uniformizer_pow_mem (ω : 𝕜) (u v : RatFunc 𝕜) (j k : ℕ)
    (hu : u/uniformizer ω ^ j ∈ regularAt ω)
    (hv : v/uniformizer ω ^ k ∈ regularAt ω) :
    (u*v)/uniformizer ω ^ (j+k) ∈ regularAt ω := by
  simpa only [pow_add, div_mul_div_comm] using (regularAt ω).mul_mem hu hv

/-- Pole bookkeeping including one additional factor with a known pole order. -/
theorem scaled_ratio_mul_mem (ω : 𝕜) (N D q : RatFunc 𝕜) (v c e w : ℕ)
    (hN : N / uniformizer ω ^ v ∈ regularAt ω)
    (hD : uniformizer ω ^ c / D ∈ regularAt ω)
    (hq : uniformizer ω ^ e * q ∈ regularAt ω) (hc : c+e ≤ w+v) :
    uniformizer ω ^ w * (N/D) * q ∈ regularAt ω := by
  have hDq : uniformizer ω ^ (c+e) / (D/q) ∈ regularAt ω := by
    have h := (regularAt ω).mul_mem hD hq
    convert h using 1
    simp only [pow_add, div_eq_mul_inv, mul_inv, inv_inv]
    ring
  have h := scaled_ratio_mem ω N (D/q) v (c+e) w hN hDq hc
  convert h using 1
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- Exact local proper-entry bound. A numerator zero order `v` compensates for
the colliding-node derivative factors and the cubic pole-tail. -/
theorem proper_term_coeff_mem [CharZero 𝕜] (ω : 𝕜) (hω : ω ≠ 0)
    (K a : ℕ) (ha : a ∈ Finset.Icc 1 K) (N : RatFunc 𝕜) (v w : ℕ)
    (hN : N / uniformizer ω ^ v ∈ regularAt ω)
    (hw : collisionCount ω K a + 3 ≤ w+v) (i : ℕ) :
    (C (uniformizer ω ^ w * (N /
        (RatFunc.X ^ a * (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X ^ a)))) *
      (X-C (S (RatFunc.X : RatFunc 𝕜) a))).coeff i ∈ regularAt ω := by
  let D : RatFunc 𝕜 := RatFunc.X ^ a *
    (derivative (F (RatFunc.X : RatFunc 𝕜) K)).eval (RatFunc.X ^ a)
  have hD : uniformizer ω ^ collisionCount ω K a / D ∈ regularAt ω := by
    have h := (regularAt ω).mul_mem (uniformizer_pow_div_derivative_mem ω hω K a ha)
      ((regularAt ω).pow_mem (inv_base_mem_regularAt ω hω) a)
    convert h using 1
    simp only [D, div_eq_mul_inv, mul_inv, inv_pow]
    ring
  have hscalar := scaled_ratio_mem ω N D v (collisionCount ω K a) w hN hD (by omega)
  have hconstant := scaled_ratio_mul_mem ω N D (S (RatFunc.X : RatFunc 𝕜) a)
    v (collisionCount ω K a) 3 w hN hD (uniformizer_cube_mul_S_mem ω hω a) hw
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub]
  by_cases hi0 : i = 0
  · subst i
    simpa only [Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, mul_neg]
      using (regularAt ω).neg_mem hconstant
  · by_cases hi1 : i = 1
    · subst i
      simpa using hscalar
    · simp [Polynomial.coeff_X, Polynomial.coeff_C, hi0, Ne.symm hi1]

theorem nrm_mem_regularAt (ω : 𝕜) (K : ℕ) :
    nrm (RatFunc.X : RatFunc 𝕜) K ∈ regularAt ω :=
  (regularAt ω).mul_mem ((regularAt ω).pow_mem ((regularAt ω).neg_mem (regularAt ω).one_mem) K)
    ((regularAt ω).pow_mem (base_mem_regularAt ω) (AK K))

theorem inv_nrm_mem_regularAt (ω : 𝕜) (hω : ω≠0) (K : ℕ) :
    (nrm (RatFunc.X : RatFunc 𝕜) K)⁻¹ ∈ regularAt ω := by
  unfold nrm
  rw [mul_inv, ← inv_pow, ← inv_pow]
  have hm : ((-1 : RatFunc 𝕜)⁻¹) = -1 := by norm_num
  rw [hm]
  exact (regularAt ω).mul_mem
    ((regularAt ω).pow_mem ((regularAt ω).neg_mem (regularAt ω).one_mem) K)
    ((regularAt ω).pow_mem (inv_base_mem_regularAt ω hω) (AK K))

end QZeta3.Generic
