import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Totient

/-!
# Imports

Single import hub for the project.  Keeping every Mathlib import in one place makes the
dependency footprint auditable: `lake build QZeta3.Imports` builds exactly the Mathlib
closure the project needs (about 2 700 of Mathlib's 8 500 modules at `v4.34.1`).
-/
