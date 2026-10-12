import QZeta3.Imports
import QZeta3.Defs
import QZeta3.Elementary
import QZeta3.Criterion
import QZeta3.Asymptotics
import QZeta3.Analytic
import QZeta3.Content
import QZeta3.Denominators
import QZeta3.Nonvanishing
import QZeta3.Frozen.Prop21
import QZeta3.Frozen.Prop31
import QZeta3.Frozen.Prop41
import QZeta3.Frozen.Prop51
import QZeta3.Main
import QZeta3.Frozen.Theorem11
import QZeta3.Consistency.Series
import QZeta3.ElementarySecondProof

/-!
# QZeta3

Lean 4 / Mathlib formalisation of the manuscript *A moving-denominator Hankel argument for the
irrationality of ζ_{1/p}(3)* (research proof candidate, 11 October 2026):

  for every integer `p ≥ 2`, `∑_{n ≥ 1} n²/(pⁿ − 1)` is irrational.

See `README.md` for the status of each part.
-/
