import QZeta3.Elementary
import QZeta3.Purity
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The determinant step in the analytic estimate

This file proves the finite-dimensional part of Proposition 2.1. The entry
estimate in the triple-root basis is proved in `QZeta3.AnalyticEntry`, and
the change-of-basis identity is proved in `QZeta3.GramBasis`.
-/

open Finset Matrix Polynomial

namespace QZeta3

/-- The monic basis with three repeated roots at each successive node. -/
noncomputable def tripleRootPoly (q : ℝ) (j : ℕ) : ℝ[X] :=
  ∏ t ∈ Icc 1 j, (Polynomial.X - Polynomial.C (q ^ ((t + 2) / 3)))

theorem tripleRootPoly_monic (q : ℝ) (j : ℕ) : (tripleRootPoly q j).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem tripleRootPoly_natDegree (q : ℝ) (j : ℕ) :
    (tripleRootPoly q j).natDegree = j := by
  unfold tripleRootPoly
  rw [Polynomial.natDegree_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _,
    Finset.sum_congr rfl fun t _ => Polynomial.natDegree_X_sub_C _]
  simp

theorem tripleRootPoly_succ (q : ℝ) (j : ℕ) :
    tripleRootPoly q (j + 1) = tripleRootPoly q j *
      (X - C (q ^ ((j + 3) / 3))) := by
  unfold tripleRootPoly
  rw [Finset.prod_Icc_succ_top (by omega)]

theorem tripleRootPoly_dvd (q : ℝ) {a b : ℕ} (hab : a ≤ b) :
    tripleRootPoly q a ∣ tripleRootPoly q b := by
  induction b, hab using Nat.le_induction with
  | base => exact dvd_refl _
  | succ b hab ih =>
    rw [tripleRootPoly_succ]
    exact dvd_mul_of_dvd_left ih _

/-- Each completed block contributes precisely a triple root. -/
theorem tripleRootPoly_block (q : ℝ) (n : ℕ) :
    tripleRootPoly q (3 * (n + 1)) =
      tripleRootPoly q (3 * n) * (X - C (q ^ (n + 1))) ^ 3 := by
  rw [show 3 * (n + 1) = ((3 * n + 1) + 1) + 1 by omega]
  rw [tripleRootPoly_succ, tripleRootPoly_succ, tripleRootPoly_succ]
  have h₁ : (3 * n + 3) / 3 = n + 1 := by omega
  have h₂ : (3 * n + 1 + 3) / 3 = n + 1 := by omega
  have h₃ : (3 * n + 1 + 1 + 3) / 3 = n + 1 := by omega
  rw [h₁, h₂, h₃]
  ring

theorem tripleRoot_dvd (q : ℝ) {m j : ℕ} (hm : 1 ≤ m) (hj : 3 * m ≤ j) :
    (X - C (q ^ m)) ^ 3 ∣ tripleRootPoly q j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  apply dvd_trans _ (tripleRootPoly_dvd q hj)
  rw [tripleRootPoly_block]
  exact dvd_mul_left _ _

/-- The three ordinary polynomial jets vanish at every completed node. -/
theorem tripleRoot_jets_vanish (q : ℝ) {m j : ℕ} (hm : 1 ≤ m) (hj : 3 * m ≤ j) :
    (tripleRootPoly q j).eval (q ^ m) = 0 ∧
      (tripleRootPoly q j).derivative.eval (q ^ m) = 0 ∧
      (tripleRootPoly q j).derivative.derivative.eval (q ^ m) = 0 := by
  obtain ⟨f, hf⟩ := tripleRoot_dvd q hm hj
  rw [hf]
  simp [Polynomial.derivative_mul, Polynomial.derivative_pow]

/-- The zeroth jet estimate at a surviving geometric node. -/
theorem tripleRoot_eval_bound {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (j m : ℕ) (hm : (j + 2) / 3 ≤ m) :
    |(tripleRootPoly q j).eval (q ^ m)| ≤ q ^ aj j := by
  unfold tripleRootPoly aj
  rw [Polynomial.eval_prod, Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀
  · intro t ht
    exact abs_nonneg _
  · intro t ht
    have htj := (Finset.mem_Icc.mp ht).2
    have htm : (t + 2) / 3 ≤ m := by omega
    have hpow : q ^ m ≤ q ^ ((t + 2) / 3) :=
      pow_le_pow_of_le_one hq0 hq1 htm
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [abs_of_nonpos (sub_nonpos.mpr hpow)]
    have : 0 ≤ q ^ m := pow_nonneg hq0 m
    linarith

/-- Scalar first-derivative step for adjoining one root. -/
theorem first_jet_product_step (x a r P n v d : ℝ)
    (ha : 0 ≤ a) (hr : a ≤ r) (hP : 0 ≤ P)
    (hxr : |x - r| ≤ r) (hv : |v| ≤ P) (hd : |d| * a ≤ n * P) :
    |d * (x - r) + v| * a ≤ (n + 1) * (P * r) := by
  have hr0 : 0 ≤ r := le_trans ha hr
  calc _ ≤ (|d| * |x - r| + |v|) * a := by
        simpa only [abs_mul] using
          mul_le_mul_of_nonneg_right (abs_add_le (d * (x - r)) v) ha
    _ ≤ (|d| * r + P) * a :=
        mul_le_mul_of_nonneg_right
          (add_le_add (mul_le_mul_of_nonneg_left hxr (abs_nonneg d)) hv) ha
    _ = (|d| * a) * r + P * a := by ring
    _ ≤ (n * P) * r + P * r :=
        add_le_add (mul_le_mul_of_nonneg_right hd hr0)
          (mul_le_mul_of_nonneg_left hr hP)
    _ = _ := by ring

/-- Scalar second-derivative step for adjoining one root. -/
theorem second_jet_product_step (x a r P n d e : ℝ)
    (ha : 0 ≤ a) (hr : a ≤ r) (hP : 0 ≤ P) (hn : 0 ≤ n)
    (hxr : |x - r| ≤ r) (hd : |d| * a ≤ n * P)
    (he : |e| * a ^ 2 ≤ n * (n - 1) * P) :
    |e * (x - r) + 2 * d| * a ^ 2 ≤ (n + 1) * n * (P * r) := by
  have hr0 : 0 ≤ r := le_trans ha hr
  have htri : |e * (x - r) + 2 * d| ≤ |e| * |x - r| + 2 * |d| := by
    simpa only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)] using
      abs_add_le (e * (x - r)) (2 * d)
  calc _ ≤ (|e| * |x - r| + 2 * |d|) * a ^ 2 :=
        mul_le_mul_of_nonneg_right htri (sq_nonneg a)
    _ ≤ (|e| * r + 2 * |d|) * a ^ 2 :=
        mul_le_mul_of_nonneg_right
          (add_le_add (mul_le_mul_of_nonneg_left hxr (abs_nonneg e)) (le_refl _)) (sq_nonneg a)
    _ = (|e| * a ^ 2) * r + 2 * (|d| * a) * a := by ring
    _ ≤ (n * (n - 1) * P) * r + 2 * (n * P) * r := by
        apply add_le_add (mul_le_mul_of_nonneg_right he hr0)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num)) hr ha
          (mul_nonneg (by norm_num) (mul_nonneg hn hP))
    _ = _ := by ring

/-- Product-rule estimates for a polynomial with positive roots, stated
without division to make the induction uniform at degree zero. -/
theorem tripleRoot_derivative_bounds {q x a : ℝ} (hq : 0 < q)
    (hx : 0 ≤ x) (ha : 0 < a) (hxa : x ≤ a) (j : ℕ)
    (hroot : ∀ t ∈ Icc 1 j, a ≤ q ^ ((t + 2) / 3)) :
    |(tripleRootPoly q j).eval x| ≤ q ^ aj j ∧
      |(tripleRootPoly q j).derivative.eval x| * a ≤ (j : ℝ) * q ^ aj j ∧
      |(tripleRootPoly q j).derivative.derivative.eval x| * a ^ 2 ≤
        (j : ℝ) * ((j : ℝ) - 1) * q ^ aj j := by
  induction j with
  | zero => simp [tripleRootPoly, aj]
  | succ j ih =>
    have hr : a ≤ q ^ ((j + 3) / 3) := hroot (j + 1) (by simp)
    have hi := ih (fun t ht => hroot t (by
      rcases Finset.mem_Icc.mp ht with ⟨ht1, htj⟩
      exact Finset.mem_Icc.mpr ⟨ht1, by omega⟩))
    let P := q ^ aj j
    let r := q ^ ((j + 3) / 3)
    let f := tripleRootPoly q j
    have hP : 0 ≤ P := (pow_pos hq _).le
    have hr0 : 0 ≤ r := (pow_pos hq _).le
    have hxr : |x - r| ≤ r := by
      rw [abs_of_nonpos (by dsimp [r]; linarith)]
      linarith
    have hpow : q ^ aj (j + 1) = P * r := by
      dsimp [P, r]
      unfold aj
      rw [Finset.sum_Icc_succ_top (by omega), pow_add]
    have he0 : (tripleRootPoly q (j + 1)).eval x = f.eval x * (x - r) := by
      rw [tripleRootPoly_succ]
      simp [f, r]
    have he1 : (tripleRootPoly q (j + 1)).derivative.eval x =
        f.derivative.eval x * (x - r) + f.eval x := by
      rw [tripleRootPoly_succ]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_sub,
        Polynomial.derivative_X, Polynomial.derivative_C, sub_zero,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, mul_one, f, r]
    have he2 : (tripleRootPoly q (j + 1)).derivative.derivative.eval x =
        f.derivative.derivative.eval x * (x - r) + 2 * f.derivative.eval x := by
      rw [tripleRootPoly_succ]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_add,
        Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
        sub_zero, mul_one,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, f, r]
      ring
    change |f.eval x| ≤ P ∧ |f.derivative.eval x| * a ≤ (j : ℝ) * P ∧
      |f.derivative.derivative.eval x| * a ^ 2 ≤ (j : ℝ) * ((j : ℝ) - 1) * P at hi
    have hb0 : |f.eval x * (x - r)| ≤ P * r := by
      rw [abs_mul]
      exact mul_le_mul hi.1 hxr (abs_nonneg _) hP
    have hb1 := first_jet_product_step x a r P j (f.eval x) (f.derivative.eval x)
      ha.le hr hP hxr hi.1 hi.2.1
    have hb2 := second_jet_product_step x a r P j (f.derivative.eval x)
      (f.derivative.derivative.eval x) ha.le hr hP (Nat.cast_nonneg j) hxr hi.2.1 hi.2.2
    rw [he0, he1, he2, hpow]
    push_cast
    exact ⟨hb0, hb1, by simpa only [add_sub_cancel_right] using hb2⟩

theorem theta_polynomial (f : ℝ[X]) (x : ℝ) :
    theta (fun y => f.eval y) x = x * f.derivative.eval x := by
  rw [theta, Polynomial.deriv]

theorem theta_sq_polynomial (f : ℝ[X]) (x : ℝ) :
    theta (theta (fun y => f.eval y)) x =
      x * f.derivative.eval x + x ^ 2 * f.derivative.derivative.eval x := by
  have he : theta (fun y => f.eval y) = fun y => y * f.derivative.eval y :=
    funext (theta_polynomial f)
  have hd : HasDerivAt (fun y => y * f.derivative.eval y)
      (1 * f.derivative.eval x + x * f.derivative.derivative.eval x) x :=
    (hasDerivAt_id x).mul (f.derivative.hasDerivAt x)
  rw [he, theta, hd.deriv]
  ring

theorem euler_jet_bounds_of_derivative_bounds (x a P n d e : ℝ)
    (hx : 0 ≤ x) (ha : 0 < a) (hxa : x ≤ a)
    (hd : |d| * a ≤ n * P) (he : |e| * a ^ 2 ≤ n * (n - 1) * P) :
    |x * d| ≤ n * P * x / a ∧
      |x * d + x ^ 2 * e| ≤ n ^ 2 * P * x / a := by
  constructor
  · rw [le_div_iff₀ ha, abs_mul, abs_of_nonneg hx]
    nlinarith [mul_le_mul_of_nonneg_left hd hx]
  · rw [le_div_iff₀ ha]
    have htri : |x * d + x ^ 2 * e| ≤ x * |d| + x ^ 2 * |e| := by
      calc _ ≤ |x * d| + |x ^ 2 * e| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hx, abs_of_nonneg (sq_nonneg x)]
    have hcompare : 0 ≤ (a - x) * x * |e| * a := by
      apply mul_nonneg _ ha.le
      exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hxa) hx) (abs_nonneg e)
    have h₁ := mul_le_mul_of_nonneg_left hd hx
    have h₂ := mul_le_mul_of_nonneg_left he hx
    have h₃ := mul_le_mul_of_nonneg_right htri ha.le
    nlinarith only [hcompare, h₁, h₂, h₃]

/-- Both surviving Euler-jet bounds, with exactly the exponents of §2. -/
theorem tripleRoot_euler_bounds {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (j m : ℕ) (hm : (j + 2) / 3 ≤ m) :
    |theta (fun x => (tripleRootPoly q j).eval x) (q ^ m)| ≤
        (j : ℝ) * q ^ aj j * q ^ m / q ^ ((j + 2) / 3) ∧
      |theta (theta (fun x => (tripleRootPoly q j).eval x)) (q ^ m)| ≤
        (j : ℝ) ^ 2 * q ^ aj j * q ^ m / q ^ ((j + 2) / 3) := by
  have hxa := pow_le_pow_of_le_one hq0.le hq1 hm
  have h := tripleRoot_derivative_bounds hq0 (pow_pos hq0 m).le
    (pow_pos hq0 _) hxa j (fun t ht =>
      pow_le_pow_of_le_one hq0.le hq1 (by
        have := (Finset.mem_Icc.mp ht).2
        omega))
  rw [theta_polynomial, theta_sq_polynomial]
  exact euler_jet_bounds_of_derivative_bounds _ _ _ _ _ _
    (pow_pos hq0 m).le (pow_pos hq0 _) hxa h.2.1 h.2.2

/-- Both Euler derivatives vanish at nodes preceding the surviving range. -/
theorem tripleRoot_euler_vanish (q : ℝ) {m j : ℕ}
    (hm : 1 ≤ m) (hj : m < (j + 2) / 3) :
    (tripleRootPoly q j).eval (q ^ m) = 0 ∧
      theta (fun x => (tripleRootPoly q j).eval x) (q ^ m) = 0 ∧
      theta (theta (fun x => (tripleRootPoly q j).eval x)) (q ^ m) = 0 := by
  obtain ⟨h₀, h₁, h₂⟩ := tripleRoot_jets_vanish q hm (by omega : 3 * m ≤ j)
  rw [theta_polynomial, theta_sq_polynomial, h₀, h₁, h₂]
  simp

/-- Coefficient matrix converting monomials into the triple-root basis. -/
noncomputable def tripleRootChange (q : ℝ) (K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  fun i j => (tripleRootPoly q i.val).coeff j.val

theorem det_tripleRootChange (q : ℝ) (K : ℕ) : (tripleRootChange q K).det = 1 := by
  have h := Matrix.det_matrixOfPolynomials (fun i : Fin K => tripleRootPoly q i.val)
    (fun i => tripleRootPoly_natDegree q i.val) (fun i => tripleRootPoly_monic q i.val)
  convert h using 1
  exact (Matrix.det_transpose _).symm

/-- Extract positive row and column weights before applying the factorial
determinant estimate. This is valid for every finite real matrix. -/
theorem abs_det_le_of_scaled_entries {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (r : n → ℝ) (M : ℝ)
    (hr : ∀ i, 0 < r i)
    (hA : ∀ i j, |A i j| ≤ M * r i * r j) :
    |A.det| ≤ (Fintype.card n).factorial * M ^ Fintype.card n * (∏ i, r i) ^ 2 := by
  let B : Matrix n n ℝ := fun i j => A i j / (r i * r j)
  have hB : ∀ i j, |B i j| ≤ M := by
    intro i j
    dsimp [B]
    rw [abs_div, abs_of_pos (mul_pos (hr i) (hr j)), div_le_iff₀ (mul_pos (hr i) (hr j))]
    simpa only [mul_assoc] using hA i j
  have hdet : |B.det| ≤ (Fintype.card n).factorial * M ^ Fintype.card n := by
    simpa only [nsmul_eq_mul, AbsoluteValue.abs_apply] using
      (Matrix.det_le (abv := AbsoluteValue.abs) hB)
  have hfactor : A = diagonal r * B * diagonal r := by
    ext i j
    calc A i j = r i * B i j * r j := by
          dsimp [B]
          field_simp [(hr i).ne', (hr j).ne']
      _ = (diagonal r * B * diagonal r) i j := by
          rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hrprod : 0 < ∏ i, r i := Finset.prod_pos fun i _ => hr i
  rw [hfactor, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    abs_mul, abs_mul, abs_of_pos hrprod]
  nlinarith [sq_nonneg (∏ i, r i), mul_le_mul_of_nonneg_right hdet (sq_nonneg (∏ i, r i))]

/-- Multiplying a matrix on both sides by a change-of-basis matrix of
determinant one preserves its Gram determinant. -/
theorem det_congruence_of_det_one {n : Type*} [Fintype n] [DecidableEq n]
    (A U : Matrix n n ℝ) (hU : U.det = 1) :
    (U * A * U.transpose).det = A.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hU]
  ring

/-- The product of the triple-root row weights has exactly the exponent
used in the original statement of Proposition 2.1. -/
theorem prod_tripleRoot_weights (p K : ℕ) :
    (∏ i : Fin K, ((p : ℝ)⁻¹) ^ aj i.val) ^ 2 = ((p : ℝ)⁻¹) ^ bK K := by
  rw [Finset.prod_pow_eq_pow_sum, ← pow_mul]
  congr 1
  simp only [bK, Fin.sum_univ_eq_sum_range]
  omega

/-- The final analytic bound follows from the transformed entry estimate.
No assertion about the analytic Gram matrix is assumed implicitly here. -/
theorem tripleRoot_det_bound (p K : ℕ) (hp : 2 ≤ p)
    (A : Matrix (Fin K) (Fin K) ℝ)
    (hA : ∀ i j, |A i j| ≤
      12 * ((i.val : ℝ) + j.val + 1) ^ 2 * ((p : ℝ)⁻¹) ^ (aj i.val + aj j.val)) :
    |A.det| ≤ (K.factorial : ℝ) * (12 * (2 * (K : ℝ) - 1) ^ 2) ^ K *
      ((p : ℝ)⁻¹) ^ bK K := by
  have hp0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast (show 0 < p by omega))
  have hentry : ∀ i j : Fin K, |A i j| ≤
      (12 * (2 * (K : ℝ) - 1) ^ 2) * ((p : ℝ)⁻¹) ^ aj i.val *
        ((p : ℝ)⁻¹) ^ aj j.val := by
    intro i j
    have hi : (i.val : ℝ) + 1 ≤ K := by exact_mod_cast i.isLt
    have hj : (j.val : ℝ) + 1 ≤ K := by exact_mod_cast j.isLt
    have hsum : 0 ≤ (i.val : ℝ) + j.val + 1 := by positivity
    have hle : (i.val : ℝ) + j.val + 1 ≤ 2 * K - 1 := by linarith
    have hsquare : ((i.val : ℝ) + j.val + 1) ^ 2 ≤ (2 * (K : ℝ) - 1) ^ 2 :=
      pow_le_pow_left₀ hsum hle 2
    calc |A i j| ≤ 12 * ((i.val : ℝ) + j.val + 1) ^ 2 *
          ((p : ℝ)⁻¹) ^ (aj i.val + aj j.val) := hA i j
      _ ≤ 12 * (2 * (K : ℝ) - 1) ^ 2 * ((p : ℝ)⁻¹) ^ (aj i.val + aj j.val) := by
        gcongr
      _ = _ := by rw [pow_add]; ring
  have h := abs_det_le_of_scaled_entries A (fun i => ((p : ℝ)⁻¹) ^ aj i.val)
    (12 * (2 * (K : ℝ) - 1) ^ 2) (fun i => pow_pos hp0 _) hentry
  simpa only [Fintype.card_fin, prod_tripleRoot_weights] using h

end QZeta3
