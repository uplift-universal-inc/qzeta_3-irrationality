import QZeta3.Elementary
import Mathlib.Topology.Algebra.InfiniteSum.Order

open Finset

namespace QZeta3

/-- Geometric tail with its initial terms suppressed. -/
noncomputable def geometricTail (q : ℝ) (R m : ℕ) : ℝ :=
  if R ≤ m + 1 then q^((m + 1) - R) else 0

theorem geometricTail_nonneg {q : ℝ} (hq : 0 ≤ q) (R m : ℕ) :
    0 ≤ geometricTail q R m := by
  unfold geometricTail
  split_ifs <;> positivity

/-- Every truncated geometric envelope has total mass at most two for `q ≤ 1/2`. -/
theorem geometricTail_sum_bound {q : ℝ} (hq0 : 0 < q) (hqhalf : q ≤ 1 / 2) (R : ℕ) :
    Summable (geometricTail q R) ∧ (∑' m : ℕ, geometricTail q R m) ≤ 2 := by
  let G : ℕ → ℝ := fun n => if R ≤ n then q^(n - R) else 0
  have hq1 : q < 1 := by linarith
  have hs : HasSum (fun n : ℕ => G (n + R)) (1 - q)⁻¹ := by
    simpa [G] using hasSum_geometric_of_lt_one hq0.le hq1
  have hzero : ∑ i ∈ range R, G i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [G, not_le.mpr (mem_range.mp hi), ite_false]
  have hG : HasSum G (1 - q)⁻¹ := by
    have ht := (hasSum_nat_add_iff (f := G) R).mp hs
    simpa only [hzero, add_zero] using ht
  have ht : Summable (geometricTail q R) := by
    change Summable (fun m : ℕ => G (m + 1))
    exact (summable_nat_add_iff (f := G) 1).mpr hG.summable
  refine ⟨ht, ?_⟩
  have hsplit := hG.summable.sum_add_tsum_nat_add 1
  simp only [sum_range_one, hG.tsum_eq] at hsplit
  have hG0 : 0 ≤ G 0 := by dsimp [G]; split_ifs <;> positivity
  have hinv : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < 1 - q)]
    linarith
  change (∑' m : ℕ, G (m + 1)) ≤ 2
  linarith

/-- Summable entries dominated by the envelope inherit its uniform total bound. -/
theorem abs_tsum_le_geometricTail {q C : ℝ} (hq0 : 0 < q) (hqhalf : q ≤ 1 / 2)
    (R : ℕ) {v : ℕ → ℝ} (hv : Summable v) (hC : 0 ≤ C)
    (hbound : ∀ m, |v m| ≤ C * geometricTail q R m) :
    |∑' m : ℕ, v m| ≤ 2 * C := by
  obtain ⟨hg, hgsum⟩ := geometricTail_sum_bound hq0 hqhalf R
  have ha : Summable (fun m => |v m|) := hv.abs
  calc |∑' m : ℕ, v m| ≤ ∑' m : ℕ, |v m| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := v) (by
          simpa only [Real.norm_eq_abs] using ha)
    _ ≤ ∑' m : ℕ, C * geometricTail q R m := ha.tsum_le_tsum hbound (hg.mul_left C)
    _ = C * ∑' m : ℕ, geometricTail q R m := tsum_mul_left
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left hgsum hC
    _ = 2 * C := mul_comm _ _

end QZeta3
