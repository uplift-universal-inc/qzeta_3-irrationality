import QZeta3.Nonvanishing

/-!
# Proposition 5.1 — infinitely many nonzero determinants (frozen statement)

Manuscript: Proposition 5.1 (`prop:normality`): the determinants `Δ_K(ξ_p)` are nonzero for
infinitely many positive integers `K`.

## How to read the formal statement

"Infinitely many `K`" is rendered as `∀ N, ∃ K ≥ N, Δ_K(ξ_p) ≠ 0`.  No sign pattern, no density
and no statement about every `K` is claimed (cf. the manuscript's scope remark).

Status: proved from the kernel-checked `gram_frequently_ne_zero` and
`gram_det_eq`.  The transitive proof uses no `sorryAx`.
-/

namespace QZeta3

variable {p : ℕ}

/-- **Proposition 5.1.**  `Δ_K(ξ_p) ≠ 0` for infinitely many `K`. -/
theorem frequently_ne_zero (hp : 2 ≤ p) : ∀ N : ℕ, ∃ K, N ≤ K ∧ DeltaR p K (xi p) ≠ 0 := by
  intro N
  obtain ⟨K, hK, h⟩ := gram_frequently_ne_zero hp N
  exact ⟨K, hK, by rwa [← gram_det_eq hp K]⟩

end QZeta3
