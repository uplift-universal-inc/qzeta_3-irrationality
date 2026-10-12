import QZeta3.CauchyMeromorphic
import QZeta3.CauchyPole

open Polynomial Filter Topology

namespace QZeta3

/-- Infinitely many genuine cubic poles exclude a rational germ at infinity. -/
theorem cauchySeries_nonrational_of_meromorphic {p : ℕ} (hp : 2 ≤ p)
    (hmeromorphic : MeromorphicOn (cauchySeries p) (Set.Ioi 0))
    (P Q : ℝ[X]) (hQ : Q ≠ 0) :
    ¬ ∀ᶠ x : ℝ in atTop, cauchySeries p x * Q.eval x - P.eval x = 0 := by
  intro hzero
  apply hQ
  apply polynomial_eq_zero_of_geometric_roots hp Q
  intro m
  have hnode : 0 < ((p : ℝ)⁻¹) ^ (m + 1) := pow_pos (inv_base_pos hp) _
  have herr : MeromorphicOn (fun x => cauchySeries p x * Q.eval x - P.eval x)
      (Set.Ioi 0) := by
    intro x hx
    exact ((hmeromorphic x hx).mul (analyticAt_polynomial_eval Q x).meromorphicAt).sub
      (analyticAt_polynomial_eval P x).meromorphicAt
  have heq := meromorphicOn_Ioi_eventually_zero_of_atTop herr hzero hnode
  apply polynomial_root_of_cubic_pole (f := cauchySeries p)
    (c := 2 * (((p : ℝ)⁻¹) ^ (m + 1)) ^ 2)
    (by positivity) (cauchySeries_cubic_pole hp m) P Q heq

/-- The actual q-Cauchy transform has no rational germ at infinity. -/
theorem cauchySeries_nonrational {p : ℕ} (hp : 2 ≤ p) (P Q : ℝ[X]) (hQ : Q ≠ 0) :
    ¬ ∀ᶠ x : ℝ in atTop, cauchySeries p x * Q.eval x - P.eval x = 0 :=
  cauchySeries_nonrational_of_meromorphic hp (meromorphicOn_cauchySeries_pos hp) P Q hQ

end QZeta3
