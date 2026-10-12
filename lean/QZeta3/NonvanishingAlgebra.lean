import QZeta3.Imports
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Algebraic part of the moving-denominator nonvanishing argument

These lemmas do not assume any q-zeta theorem.  They isolate the polynomial
arguments in Proposition 5.1: uniqueness without division at interpolation
nodes, propagation through a singular tail, extraction of common factors,
and the final contradiction from a bounded degree and increasing root count.

The analytic inputs needed to apply them to `gramR` are deliberately stated
as hypotheses; this file does not claim to establish those inputs.
-/

open Polynomial Filter Topology Asymptotics

namespace QZeta3.NonvanishingAlgebra

/-- A singular moment matrix supplies a nonzero orthogonal polynomial with
the exact degree bound needed in the interpolation argument. -/
theorem exists_orthogonal_polynomial {n : ℕ} (hn : 0 < n)
    (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hdet : (Matrix.of fun i j : Fin n => L (Polynomial.X ^ (i.val + j.val))).det = 0) :
    ∃ Q : ℝ[X], Q ≠ 0 ∧ Q.natDegree < n ∧
      ∀ j : Fin n, L (Polynomial.X ^ j.val * Q) = 0 := by
  classical
  obtain ⟨v, hv, hkernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let Q : ℝ[X] := ∑ i : Fin n, v i • Polynomial.X ^ i.val
  have hcoeff : ∀ i : Fin n, Q.coeff i.val = v i := by
    intro i
    simp [Q, Polynomial.coeff_X_pow, ← Fin.ext_iff]
  have hQ : Q ≠ 0 := by
    intro h
    apply hv
    ext i
    simpa [h] using (hcoeff i).symm
  have hdegree : Q.natDegree ≤ n - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    apply (Polynomial.natDegree_smul_le (v i) (Polynomial.X ^ i.val)).trans
    simp only [Polynomial.natDegree_X_pow]
    omega
  refine ⟨Q, hQ, by omega, ?_⟩
  intro j
  have hterm : ∀ i : Fin n, (Polynomial.X : ℝ[X]) ^ j.val *
      (v i • Polynomial.X ^ i.val) = v i • Polynomial.X ^ (j.val + i.val) := by
    intro i
    rw [mul_smul_comm, pow_add]
  have hkernelj := congrFun hkernel j
  simpa [Q, Finset.mul_sum, hterm, map_sum, map_smul, Matrix.mulVec,
    dotProduct, mul_comm] using hkernelj

/-- A polynomial growing strictly slower than `xⁿ` has degree below `n`. -/
theorem natDegree_lt_of_isLittleO_pow (P : ℝ[X]) {n : ℕ} (hn : 0 < n)
    (hP : P.eval =o[atTop] (fun x : ℝ => x ^ n)) : P.natDegree < n := by
  by_cases hzero : P = 0
  · simpa [hzero] using hn
  by_contra hdegree
  have hle : n ≤ P.natDegree := by omega
  have hbig : (fun x : ℝ => x ^ n) =O[atTop] P.eval := by
    simpa using (Polynomial.X ^ n : ℝ[X]).isBigO_atTop_of_degree_le P
      (by simpa [Polynomial.degree_eq_natDegree hzero] using hle)
  have hfrequent : ∃ᶠ x in atTop, P.eval x ≠ 0 :=
    (P.eventually_atTop_not_isRoot hzero).frequently
  exact Asymptotics.isLittleO_irrefl hfrequent (hP.trans_isBigO hbig)

/-- A polynomial of degree at most `n`, times an error tending to zero,
is little-o of `xⁿ`. -/
theorem mul_error_isLittleO_pow (Q : ℝ[X]) (n : ℕ) (E : ℝ → ℝ)
    (hdegree : Q.natDegree ≤ n) (hE : Tendsto E atTop (𝓝 0)) :
    (fun x => Q.eval x * E x) =o[atTop] (fun x => x ^ n) := by
  have hQ : Q.eval =O[atTop] (fun x : ℝ => x ^ n) := by
    simpa using Q.isBigO_atTop_of_degree_le (Polynomial.X ^ n)
      (by simpa using Polynomial.degree_le_of_natDegree_le hdegree)
  have hE' : E =o[atTop] (fun _ : ℝ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr hE
  simpa using hQ.mul_isLittleO hE'

/-- The degree drop in the cross product of consecutive approximants follows
just from convergence of both approximation errors to zero. -/
theorem cross_natDegree_lt (F : ℝ → ℝ) (P Q R S : ℝ[X])
    {n : ℕ} (hn : 0 < n) (hQ : Q.natDegree ≤ n) (hS : S.natDegree ≤ n)
    (hfirst : Tendsto (fun x => F x * Q.eval x - P.eval x) atTop (𝓝 0))
    (hsecond : Tendsto (fun x => F x * S.eval x - R.eval x) atTop (𝓝 0)) :
    (R * Q - P * S).natDegree < n := by
  apply natDegree_lt_of_isLittleO_pow _ hn
  convert (mul_error_isLittleO_pow S n _ hS hfirst).sub
    (mul_error_isLittleO_pow Q n _ hQ hsecond) using 1
  ext x
  simp only [Polynomial.eval_sub, Polynomial.eval_mul]
  ring

/-- Uniqueness of consecutive rational interpolants.  No polynomial value
at an interpolation node is required to be nonzero. -/
theorem cross_eq_of_interpolation {n : ℕ} (F : ℝ → ℝ)
    (t : Fin n → ℝ) (ht : Function.Injective t)
    (P Q R S : ℝ[X])
    (hdegree : (R * Q - P * S).natDegree < n)
    (hfirst : ∀ i, F (t i) * Q.eval (t i) - P.eval (t i) = 0)
    (hsecond : ∀ i, F (t i) * S.eval (t i) - R.eval (t i) = 0) :
    R * Q = P * S := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (R * Q - P * S) ht
  · intro i
    simp only [Polynomial.eval_sub, Polynomial.eval_mul]
    have hP := hfirst i
    have hR := hsecond i
    rw [← sub_eq_zero.mp hP, ← sub_eq_zero.mp hR]
    ring
  · simpa using hdegree

/-- Analytic uniqueness of consecutive rational interpolants, with the
polynomial degree bound derived rather than assumed. -/
theorem cross_eq_of_errors_tendsto {n : ℕ} (hn : 0 < n) (F : ℝ → ℝ)
    (t : Fin n → ℝ) (ht : Function.Injective t)
    (P Q R S : ℝ[X]) (hQ : Q.natDegree ≤ n) (hS : S.natDegree ≤ n)
    (hfirstLimit : Tendsto (fun x => F x * Q.eval x - P.eval x) atTop (𝓝 0))
    (hsecondLimit : Tendsto (fun x => F x * S.eval x - R.eval x) atTop (𝓝 0))
    (hfirst : ∀ i, F (t i) * Q.eval (t i) - P.eval (t i) = 0)
    (hsecond : ∀ i, F (t i) * S.eval (t i) - R.eval (t i) = 0) :
    R * Q = P * S :=
  cross_eq_of_interpolation F t ht P Q R S
    (cross_natDegree_lt F P Q R S hn hQ hS hfirstLimit hsecondLimit)
    hfirst hsecond

/-- Equality of fractions is transitive without any evaluation or division. -/
theorem cross_eq_trans {P₁ Q₁ P₂ Q₂ P₃ Q₃ : ℝ[X]}
    (hQ₂ : Q₂ ≠ 0) (h₁₂ : P₁ * Q₂ = P₂ * Q₁)
    (h₂₃ : P₂ * Q₃ = P₃ * Q₂) : P₁ * Q₃ = P₃ * Q₁ := by
  apply mul_right_cancel₀ hQ₂
  calc
    P₁ * Q₃ * Q₂ = (P₁ * Q₂) * Q₃ := by ring
    _ = (P₂ * Q₁) * Q₃ := by rw [h₁₂]
    _ = (P₂ * Q₃) * Q₁ := by ring
    _ = (P₃ * Q₂) * Q₁ := by rw [h₂₃]
    _ = P₃ * Q₁ * Q₂ := by ring

/-- Consecutive equalities force a single rational approximant on a tail. -/
theorem cross_eq_on_tail (P Q : ℕ → ℝ[X]) (N : ℕ)
    (hQ : ∀ n, N ≤ n → Q n ≠ 0)
    (hstep : ∀ n, N ≤ n → P n * Q (n + 1) = P (n + 1) * Q n) :
    ∀ n, N ≤ n → P N * Q n = P n * Q N := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      exact cross_eq_trans (hQ n hn) ih (hstep n hn)

/-- A common reduced fraction divides both components of every equal pair. -/
theorem factor_pair_of_coprime (P Q P' Q' : ℝ[X])
    (hQ : Q ≠ 0) (hQ' : Q' ≠ 0) (hcoprime : IsCoprime P Q)
    (hcross : P * Q' = P' * Q) :
    ∃ U : ℝ[X], U ≠ 0 ∧ Q' = U * Q ∧ P' = U * P := by
  have hdiv : Q ∣ P * Q' := by
    rw [hcross]
    exact dvd_mul_left Q P'
  obtain ⟨U, hU⟩ := hcoprime.symm.dvd_of_dvd_mul_left hdiv
  have hQ'U : Q' = U * Q := hU.trans (mul_comm Q U)
  have hUne : U ≠ 0 := by
    intro h
    exact hQ' (by simpa [h] using hQ'U)
  refine ⟨U, hUne, hQ'U, ?_⟩
  apply mul_right_cancel₀ hQ
  calc
    P' * Q = P * Q' := hcross.symm
    _ = P * (U * Q) := by rw [hQ'U]
    _ = U * P * Q := by ring

/-- Every polynomial fraction with nonzero denominator has a reduced pair. -/
theorem exists_coprime_pair (P Q : ℝ[X]) (hQ : Q ≠ 0) :
    ∃ P₀ Q₀ : ℝ[X], Q₀ ≠ 0 ∧ IsCoprime P₀ Q₀ ∧ P₀ * Q = P * Q₀ := by
  obtain ⟨P₀, Q₀, hP₀, hQ₀, hcoprime⟩ := extract_gcd P Q
  have hQ₀ne : Q₀ ≠ 0 := by
    intro h
    exact hQ (by simpa [h] using hQ₀)
  refine ⟨P₀, Q₀, hQ₀ne, (gcd_isUnit_iff P₀ Q₀).mp hcoprime, ?_⟩
  calc
    P₀ * Q = P₀ * (gcd P Q * Q₀) := congrArg (P₀ * ·) hQ₀
    _ = (gcd P Q * P₀) * Q₀ := by ring
    _ = P * Q₀ := congrArg (· * Q₀) hP₀.symm

/-- Dividing an error tending to zero by a nonzero polynomial preserves
convergence to zero at positive infinity. -/
theorem tendsto_zero_of_polynomial_mul (U : ℝ[X]) (hU : U ≠ 0)
    (E : ℝ → ℝ) (hUE : Tendsto (fun x => U.eval x * E x) atTop (𝓝 0)) :
    Tendsto E atTop (𝓝 0) := by
  have hbig : (fun _ : ℝ => (1 : ℝ)) =O[atTop] U.eval := by
    simpa using (1 : ℝ[X]).isBigO_atTop_of_degree_le U
      (by simp [Polynomial.degree_eq_natDegree hU])
  have hbigE : E =O[atTop] (fun x => U.eval x * E x) := by
    simpa using hbig.mul (Asymptotics.isBigO_refl E atTop)
  exact hbigE.trans_tendsto hUE

/-- A nonzero polynomial cannot vanish on more distinct nodes than its degree. -/
theorem false_of_bounded_degree_roots (t : ℕ → ℝ) (ht : Function.Injective t)
    (N A d : ℕ) (U : ℕ → ℝ[X])
    (hU : ∀ n, N ≤ n → U n ≠ 0)
    (hdegree : ∀ n, N ≤ n → (U n).natDegree ≤ d)
    (hzero : ∀ n a, N ≤ n → A ≤ a → a < n → (U n).eval (t a) = 0) :
    False := by
  let n := max N (A + d + 1)
  have hn : N ≤ n := le_max_left _ _
  have hlarge : A + d + 1 ≤ n := le_max_right _ _
  have hnodes : Function.Injective (fun i : Fin (d + 1) => t (A + i.val)) := by
    intro i j hij
    apply Fin.ext
    exact Nat.add_left_cancel (ht hij)
  have hpoly : U n = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (U n) hnodes
    · intro i
      exact hzero n (A + i.val) hn (by omega) (by omega)
    · simpa using Nat.lt_succ_of_le (hdegree n hn)
  exact hU n hn hpoly

/-- The final root-count contradiction, applied to the errors `Uₙ E`.
Eventual nonvanishing of `E` at the nodes comes from its first nonzero
Laurent coefficient at infinity in the analytic argument. -/
theorem false_of_bounded_degree_errors (t : ℕ → ℝ) (ht : Function.Injective t)
    (E : ℝ → ℝ) (N A d : ℕ) (U : ℕ → ℝ[X])
    (hU : ∀ n, N ≤ n → U n ≠ 0)
    (hdegree : ∀ n, N ≤ n → (U n).natDegree ≤ d)
    (hE : ∀ a, A ≤ a → E (t a) ≠ 0)
    (hzero : ∀ n a, N ≤ n → a < n → (U n).eval (t a) * E (t a) = 0) :
    False := by
  apply false_of_bounded_degree_roots t ht N A d U hU hdegree
  intro n a hn ha han
  exact (mul_eq_zero.mp (hzero n a hn han)).resolve_right (hE a ha)

/-- A nonzero Laurent limit and a vanishing product bound the degree of
the polynomial multiplier. -/
theorem natDegree_lt_of_laurent_limit (U : ℝ[X]) (hU : U ≠ 0)
    (E : ℝ → ℝ) (h : ℕ) (c : ℝ) (hc : c ≠ 0)
    (hE : Tendsto (fun x : ℝ => x ^ h * E x) atTop (𝓝 c))
    (hUE : Tendsto (fun x => U.eval x * E x) atTop (𝓝 0)) :
    U.natDegree < h := by
  by_contra hdegree
  have hle : h ≤ U.natDegree := by omega
  have hbig : (fun x : ℝ => x ^ h) =O[atTop] U.eval := by
    simpa using (Polynomial.X ^ h : ℝ[X]).isBigO_atTop_of_degree_le U
      (by simpa [Polynomial.degree_eq_natDegree hU] using hle)
  have hbigE : (fun x : ℝ => x ^ h * E x) =O[atTop]
      (fun x => U.eval x * E x) := hbig.mul (Asymptotics.isBigO_refl E atTop)
  exact hc (tendsto_nhds_unique hE (hbigE.trans_tendsto hUE))

/-- A nonzero Laurent leading coefficient prevents zeros sufficiently far
along any sequence escaping to positive infinity. -/
theorem eventually_ne_zero_of_laurent_limit (E : ℝ → ℝ) (h : ℕ) (c : ℝ)
    (hc : c ≠ 0) (hE : Tendsto (fun x : ℝ => x ^ h * E x) atTop (𝓝 c))
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) :
    ∃ A : ℕ, ∀ a, A ≤ a → E (t a) ≠ 0 := by
  have hnonzero : ∀ᶠ a in atTop, (t a) ^ h * E (t a) ≠ 0 :=
    (hE.comp ht).eventually (isOpen_ne.mem_nhds hc)
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.1 hnonzero
  refine ⟨A, fun a ha => ?_⟩
  exact (mul_ne_zero_iff.mp (hA a ha)).2

/-- The final normality contradiction with its degree and eventual
nonvanishing conclusions derived from one Laurent limit. -/
theorem false_of_laurent_limit_errors (t : ℕ → ℝ) (ht : Function.Injective t)
    (htop : Tendsto t atTop atTop) (E : ℝ → ℝ) (N h : ℕ) (c : ℝ)
    (hc : c ≠ 0) (hE : Tendsto (fun x : ℝ => x ^ h * E x) atTop (𝓝 c))
    (U : ℕ → ℝ[X]) (hU : ∀ n, N ≤ n → U n ≠ 0)
    (hlimit : ∀ n, N ≤ n →
      Tendsto (fun x => (U n).eval x * E x) atTop (𝓝 0))
    (hzero : ∀ n a, N ≤ n → a < n → (U n).eval (t a) * E (t a) = 0) :
    False := by
  obtain ⟨A, hA⟩ := eventually_ne_zero_of_laurent_limit E h c hc hE t htop
  apply false_of_bounded_degree_errors t ht E N A h U hU
    (fun n hn => Nat.le_of_lt (natDegree_lt_of_laurent_limit (U n) (hU n hn)
      E h c hc hE (hlimit n hn))) hA hzero

/-- Normality for nested rational interpolants.  The analytic hypothesis
`hnonflat` says that a nonzero polynomial denominator cannot make the error
flat at infinity: every error tending to zero has a first nonzero Laurent
coefficient.  This is precisely the remaining consequence of analyticity
at infinity and nonrationality required by the manuscript argument.

The conclusion rules out an entire tail of singular sizes once a kernel
polynomial at each singular size has supplied the displayed degree,
interpolation, and convergence properties. -/
theorem no_tail_of_interpolants (F : ℝ → ℝ) (t : ℕ → ℝ)
    (ht : Function.Injective t) (htop : Tendsto t atTop atTop)
    (hnonflat : ∀ P Q : ℝ[X], Q ≠ 0 →
      Tendsto (fun x => F x * Q.eval x - P.eval x) atTop (𝓝 0) →
      ∃ h : ℕ, ∃ c : ℝ, c ≠ 0 ∧
        Tendsto (fun x : ℝ => x ^ h * (F x * Q.eval x - P.eval x)) atTop (𝓝 c))
    (N : ℕ) (hN : 0 < N) (P Q : ℕ → ℝ[X])
    (hQ : ∀ n, N ≤ n → Q n ≠ 0)
    (hdegree : ∀ n, N ≤ n → (Q n).natDegree < n)
    (hlimit : ∀ n, N ≤ n →
      Tendsto (fun x => F x * (Q n).eval x - (P n).eval x) atTop (𝓝 0))
    (hzero : ∀ n a, N ≤ n → a < n →
      F (t a) * (Q n).eval (t a) - (P n).eval (t a) = 0) :
    False := by
  classical
  have hstep : ∀ n, N ≤ n → P n * Q (n + 1) = P (n + 1) * Q n := by
    intro n hn
    apply Eq.symm
    apply cross_eq_of_errors_tendsto (by omega) F (fun i : Fin n => t i.val)
      (ht.comp Fin.val_injective) (P n) (Q n) (P (n + 1)) (Q (n + 1))
      (by have := hdegree n hn; omega)
      (by have := hdegree (n + 1) (by omega); omega)
      (hlimit n hn) (hlimit (n + 1) (by omega))
    · intro i
      exact hzero n i.val hn i.isLt
    · intro i
      exact hzero (n + 1) i.val (by omega) (by omega)
  have hsame := cross_eq_on_tail P Q N hQ hstep
  obtain ⟨P₀, Q₀, hQ₀, hcoprime, hcross⟩ := exists_coprime_pair (P N) (Q N) (hQ N le_rfl)
  have hsame₀ : ∀ n, N ≤ n → P₀ * Q n = P n * Q₀ := by
    intro n hn
    exact cross_eq_trans (hQ N le_rfl) hcross (hsame n hn)
  have hfactors : ∀ n, N ≤ n → ∃ U : ℝ[X],
      U ≠ 0 ∧ Q n = U * Q₀ ∧ P n = U * P₀ := by
    intro n hn
    exact factor_pair_of_coprime P₀ Q₀ (P n) (Q n) hQ₀ (hQ n hn)
      hcoprime (hsame₀ n hn)
  let U : ℕ → ℝ[X] := fun n => if hn : N ≤ n then (hfactors n hn).choose else 1
  have hU : ∀ n, N ≤ n → U n ≠ 0 ∧ Q n = U n * Q₀ ∧ P n = U n * P₀ := by
    intro n hn
    simpa only [U, dite_eq_left hn] using (hfactors n hn).choose_spec
  let E : ℝ → ℝ := fun x => F x * Q₀.eval x - P₀.eval x
  have herror : ∀ n, N ≤ n → ∀ x,
      (U n).eval x * E x = F x * (Q n).eval x - (P n).eval x := by
    intro n hn x
    rw [(hU n hn).2.1, (hU n hn).2.2]
    simp only [Polynomial.eval_mul, E]
    ring
  have hUE : ∀ n, N ≤ n → Tendsto (fun x => (U n).eval x * E x) atTop (𝓝 0) := by
    intro n hn
    simpa only [herror n hn] using hlimit n hn
  have hE : Tendsto E atTop (𝓝 0) :=
    tendsto_zero_of_polynomial_mul (U N) (hU N le_rfl).1 E (hUE N le_rfl)
  obtain ⟨h, c, hc, hleading⟩ := hnonflat P₀ Q₀ hQ₀ hE
  apply false_of_laurent_limit_errors t ht htop E N h c hc hleading U
    (fun n hn => (hU n hn).1) hUE
  intro n a hn ha
  rw [herror n hn]
  exact hzero n a hn ha

/-- General moving-moment normality theorem.  The q-specific analysis only
needs to provide the Cauchy-transform nonflatness and the interpolation
identity with its vanishing error for each orthogonal polynomial. -/
theorem frequently_nonsingular_moment_matrix (F : ℝ → ℝ) (t : ℕ → ℝ)
    (ht : Function.Injective t) (htop : Tendsto t atTop atTop)
    (L : ℕ → (ℝ[X] →ₗ[ℝ] ℝ))
    (hnonflat : ∀ P Q : ℝ[X], Q ≠ 0 →
      Tendsto (fun x => F x * Q.eval x - P.eval x) atTop (𝓝 0) →
      ∃ h : ℕ, ∃ c : ℝ, c ≠ 0 ∧
        Tendsto (fun x : ℝ => x ^ h * (F x * Q.eval x - P.eval x)) atTop (𝓝 c))
    (hinterpolant : ∀ n, 0 < n → ∀ Q : ℝ[X], Q ≠ 0 → Q.natDegree < n →
      (∀ j : Fin n, L n (Polynomial.X ^ j.val * Q) = 0) →
      ∃ P : ℝ[X],
        Tendsto (fun x => F x * Q.eval x - P.eval x) atTop (𝓝 0) ∧
        ∀ a, a < n → F (t a) * Q.eval (t a) - P.eval (t a) = 0) :
    ∀ N : ℕ, ∃ n, N ≤ n ∧
      (Matrix.of fun i j : Fin n => L n (Polynomial.X ^ (i.val + j.val))).det ≠ 0 := by
  classical
  intro N
  by_contra h
  push Not at h
  let N' := max N 1
  have hN' : 0 < N' := by dsimp [N']; omega
  have hpairs : ∀ n, N' ≤ n → ∃ P Q : ℝ[X],
      Q ≠ 0 ∧ Q.natDegree < n ∧
      Tendsto (fun x => F x * Q.eval x - P.eval x) atTop (𝓝 0) ∧
      ∀ a, a < n → F (t a) * Q.eval (t a) - P.eval (t a) = 0 := by
    intro n hn
    have hnpos : 0 < n := by omega
    have hNn : N ≤ n := (le_max_left N 1).trans hn
    obtain ⟨Q, hQ, hdegree, horth⟩ := exists_orthogonal_polynomial hnpos (L n) (h n hNn)
    obtain ⟨P, hlimit, hzero⟩ := hinterpolant n hnpos Q hQ hdegree horth
    exact ⟨P, Q, hQ, hdegree, hlimit, hzero⟩
  let P : ℕ → ℝ[X] := fun n => if hn : N' ≤ n then (hpairs n hn).choose else 0
  let Q : ℕ → ℝ[X] := fun n => if hn : N' ≤ n then
    (hpairs n hn).choose_spec.choose else 1
  have hpair : ∀ n, N' ≤ n → Q n ≠ 0 ∧ (Q n).natDegree < n ∧
      Tendsto (fun x => F x * (Q n).eval x - (P n).eval x) atTop (𝓝 0) ∧
      ∀ a, a < n → F (t a) * (Q n).eval (t a) - (P n).eval (t a) = 0 := by
    intro n hn
    simpa only [P, Q, dite_eq_left hn] using (hpairs n hn).choose_spec.choose_spec
  exact no_tail_of_interpolants F t ht htop hnonflat N' hN' P Q
    (fun n hn => (hpair n hn).1)
    (fun n hn => (hpair n hn).2.1)
    (fun n hn => (hpair n hn).2.2.1)
    (fun n a hn ha => (hpair n hn).2.2.2 a ha)

/-- The exterior nodes `p, p², …` are distinct for every integer `p ≥ 2`. -/
theorem exterior_nodes_injective {p : ℕ} (hp : 2 ≤ p) :
    Function.Injective (fun a : ℕ => (p : ℝ) ^ (a + 1)) := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  intro a b hab
  have := (pow_right_strictMono₀ hp').injective hab
  omega

/-- The exterior interpolation nodes escape to positive infinity. -/
theorem exterior_nodes_tendsto {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ => (p : ℝ) ^ (a + 1)) atTop atTop := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  exact (tendsto_pow_atTop_atTop_of_one_lt hp').comp
    (tendsto_add_atTop_nat 1)

end QZeta3.NonvanishingAlgebra
