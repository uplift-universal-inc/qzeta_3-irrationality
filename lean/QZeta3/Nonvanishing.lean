import QZeta3.Analytic
import QZeta3.CauchyInterpolation
import QZeta3.CauchyNonrational
import QZeta3.NonvanishingAnalytic

/-!
# Infinitely many nonzero determinants (Proposition 5.1): route

**Status:** `gram_frequently_ne_zero` is proved; the identity `cauchyF_eq`
(and the computation `θ²((z − x)⁻¹) = x(z+x)/(z−x)³`) is proved.  Proposition 5.1 itself
(`frequently_ne_zero`) is stated in `QZeta3.Frozen.Prop51` and follows from it and
`gram_det_eq`.

The general interpolation normality argument is proved in
`QZeta3.NonvanishingAlgebra.no_tail_of_interpolants`.  The q-specific
interpolants, the nonzero Laurent limit, and the exclusion of rational
germs using infinitely many genuine cubic poles are also kernel checked.

* `cauchyF` : the Cauchy transform `𝓕(z) = L((z − x)⁻¹) = ∑_{m ≥ 1} q^m (z + q^m)/(z − q^m)³`
  (eq. (5.1)), defined for `z` outside the support `{q^m}`.
* `gram_frequently_ne_zero` : the real Gram determinant is nonzero for infinitely many sizes.

## Proof route (manuscript §5)

`𝓕` has a genuine pole of order three at every `q^m`, so it is not a rational function.  If the
Gram matrix of size `n` is singular, a kernel vector gives a polynomial `Q_n ≠ 0` of degree `< n`
with `L(x^j Q_n/D_n) = 0` for `j < n`; the rational interpolation identity
`𝓕 Q_n − T_n = D_n · L(Q_n(x)/((z − x) D_n(x)))` (eq. (5.4)) then gives an error
`E_n = 𝓕 Q_n − T_n = O(1/z)` vanishing at the exterior nodes `p, …, p^n`.  Two consecutive
singular sizes force `T_n/Q_n = T_{n+1}/Q_{n+1}` (a polynomial of degree `≤ n−1` with `n` zeros
vanishes).  An eventually singular tail would give one reduced `T/Q`, hence a nonzero
`E = 𝓕Q − T` with a zero of finite order `h` at infinity, forcing `deg U_n ≤ h − 1` for the
multipliers `U_n = Q_n/Q` while `U_n` must vanish at all large exterior nodes: contradiction.
No sign pattern and no statement about every `K` is used.
-/

open Finset Filter Topology

namespace QZeta3

variable {p : ℕ}

/-- Singularity of the actual moving Gram matrix gives the orthogonal
polynomial used by the normality argument. -/
theorem gram_singular_orthogonal (hp : 2 ≤ p) {n : ℕ} (hn : 0 < n)
    (hsingular : (gramR p n).det = 0) :
    ∃ Q : Polynomial ℝ, Q ≠ 0 ∧ Q.natDegree < n ∧
      ∀ j : Fin n, Lfun p (fun x => x ^ j.val * Q.eval x / DK p n x) = 0 := by
  have hmoment : (Matrix.of fun i j : Fin n =>
      numeratorFunctional hp n (Polynomial.X ^ (i.val + j.val))).det = 0 := by
    simpa [numeratorFunctional, gramR] using hsingular
  obtain ⟨Q, hQ, hdegree, horth⟩ :=
    NonvanishingAlgebra.exists_orthogonal_polynomial hn (numeratorFunctional hp n) hmoment
  refine ⟨Q, hQ, hdegree, ?_⟩
  intro j
  simpa [numeratorFunctional] using horth j

/-- Analytic interface for Proposition 5.1.  All linear
algebra, polynomial stabilization, Laurent-order, and root-count steps are
proved by this reduction.  The following results discharge its hypotheses
for the actual q-functional. -/
theorem gram_frequently_ne_zero_of_cauchy_data (hp : 2 ≤ p)
    (hmeromorphic : MeromorphicAt (fun u : ℝ => cauchyF p u⁻¹) 0)
    (hnonrational : ∀ P Q : Polynomial ℝ, Q ≠ 0 →
      ¬ ∀ᶠ x : ℝ in atTop, cauchyF p x * Q.eval x - P.eval x = 0)
    (hinterpolant : ∀ n, 0 < n → ∀ Q : Polynomial ℝ, Q ≠ 0 → Q.natDegree < n →
      (∀ j : Fin n, Lfun p (fun x => x ^ j.val * Q.eval x / DK p n x) = 0) →
      ∃ P : Polynomial ℝ,
        Tendsto (fun x => cauchyF p x * Q.eval x - P.eval x) atTop (𝓝 0) ∧
        ∀ a, a < n → cauchyF p ((p : ℝ) ^ (a + 1)) *
          Q.eval ((p : ℝ) ^ (a + 1)) - P.eval ((p : ℝ) ^ (a + 1)) = 0) :
    ∀ N : ℕ, ∃ K, N ≤ K ∧ (gramR p K).det ≠ 0 := by
  have h := NonvanishingAlgebra.frequently_nonsingular_of_meromorphic_nonrational
    (cauchyF p) (fun a : ℕ => (p : ℝ) ^ (a + 1))
    (NonvanishingAlgebra.exterior_nodes_injective hp)
    (NonvanishingAlgebra.exterior_nodes_tendsto hp)
    (numeratorFunctional hp) hmeromorphic hnonrational
    (by simpa [numeratorFunctional] using hinterpolant)
  simpa [numeratorFunctional, gramR] using h

/-- Normality reduced to the nonrationality of the Cauchy germ, with every
other analytic input discharged for the actual q-functional. -/
theorem gram_frequently_ne_zero_of_nonrational (hp : 2 ≤ p)
    (hnonrational : ∀ P Q : Polynomial ℝ, Q ≠ 0 →
      ¬ ∀ᶠ x : ℝ in atTop, cauchyF p x * Q.eval x - P.eval x = 0) :
    ∀ N : ℕ, ∃ K, N ≤ K ∧ (gramR p K).det ≠ 0 := by
  apply gram_frequently_ne_zero_of_cauchy_data hp
    (meromorphicAt_cauchySeries_inv hp) hnonrational
  intro n hn Q hQ hdegree horth
  exact cauchy_orthogonal_interpolant hp n Q horth

/-- The real Gram determinant is nonzero for infinitely many sizes (§5). -/
theorem gram_frequently_ne_zero (hp : 2 ≤ p) : ∀ N : ℕ, ∃ K, N ≤ K ∧ (gramR p K).det ≠ 0 := by
  apply gram_frequently_ne_zero_of_nonrational hp
  exact cauchySeries_nonrational hp

end QZeta3
