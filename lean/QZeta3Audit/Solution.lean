import QZeta3.Frozen.Theorem11
import QZeta3.Consistency.Series

/-!
# Comparator solution: the main theorem from the library

Proves the Mathlib-only statement of `QZeta3Audit/Challenge.lean` from `QZeta3.theorem11`.
-/

namespace QZeta3Challenge

theorem irrational_qzeta3 (p : ℕ) (hp : 2 ≤ p) :
    Irrational (∑' n : ℕ, ((n : ℝ) + 1) ^ 2 / ((p : ℝ) ^ (n + 1) - 1)) := by
  rw [← QZeta3.xi_eq_tsum]
  exact QZeta3.theorem11 p hp

end QZeta3Challenge
