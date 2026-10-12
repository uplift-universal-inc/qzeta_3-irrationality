import QZeta3.Imports

/-!
# Definitions

The objects of the manuscript *A moving-denominator Hankel argument for the irrationality of
ζ_{1/p}(3)* (research proof candidate, 11 October 2026), §1, §3 and §4, in the form used by the
formal development.  Equation numbers refer to that manuscript.

* `QZeta3.term p n`, `QZeta3.xi p` : the real number ξ_p = ∑_{n ≥ 1} n²/(pⁿ − 1) (Theorem 1.1).
* `QZeta3.mu p j` : the polynomial moments μ_j = j²/(p^j − 1), μ_0 = L(1) = 0 (eq. (1.4)).
* `QZeta3.S p a` : S_a = ∑_{b ≤ a} p^b (p^b + 1)/(p^b − 1)³ (eq. (1.5)).
* `QZeta3.F p K` : F_K(x) = ∏_{a=1}^K (x − p^a), monic, with D_K = (−1)^K p^{−A_K} F_K (§3).
* `QZeta3.res`, `QZeta3.mConst`, `QZeta3.mLin` : the affine polynomial M_k(X) = L_X(x^k/F_K)
  written as `mConst + mLin * X`, computed by polynomial division and partial fractions
  (§3: quotient of x^k by F_K, residues r_a^k/F_K'(r_a), and L_X((x − r_a)⁻¹) = −(X − S_a)/r_a).
* `QZeta3.Delta p K` : Δ_K(X) = det [L_X(x^{i+j}/D_K)]_{0 ≤ i,j < K} ∈ ℚ[X] (eq. (1.7)).
* `QZeta3.DeltaR p K x` : Δ_K evaluated at a real number x.
* `QZeta3.AK`, `QZeta3.eK` : A_K = K(K+1)/2 and e_K = K(K²−1)/2 = A_K(K−1) (eq. (1.8)).
* `QZeta3.aj`, `QZeta3.bK` : a_j = ∑_{t ≤ j} ⌈t/3⌉ and b_K = 2 ∑_{j<K} a_j (Proposition 2.1).
* `QZeta3.Phi`, `QZeta3.cMain`, `QZeta3.cApp`, `QZeta3.CK` : `Φ_d(p)` and the cyclotomic multiplier C_K = ∏ Φ_d(p)^{c_{K,d}}
  (eq. (4.1)–(4.2); `cApp` is the stronger Appendix A exponent 5(K−d)+3).

The manuscript's formal variable `X` is the polynomial variable `X` of `ℚ[X]`.

## Statement-fidelity notes

* `xi` is a `tsum`.  In Mathlib a non-summable `tsum` is `0`, so `QZeta3.summable_term`
  (proved in `QZeta3.Elementary`) is part of the fidelity audit: it shows that `xi p` really is
  the convergent series of the theorem and not the junk value.
* The index of `xi` is shifted by one so that the `n = 0` term, which would be `0 / 0`, never
  appears.
* `AK` uses natural-number division, which is exact (`K(K+1)` is even); `QZeta3.AK_cast` and
  `QZeta3.eK_cast` (in `QZeta3.Elementary`) record the exact identities over `ℝ`.
-/

open Polynomial Finset

namespace QZeta3

/-! ### The real number ξ_p -/

/-- The `n`-th term `n² / (pⁿ − 1)` of the series defining `ξ_p`. -/
noncomputable def term (p : ℕ) (n : ℕ) : ℝ := (n : ℝ) ^ 2 / ((p : ℝ) ^ n - 1)

/-- `ξ_p = ∑_{n ≥ 1} n²/(pⁿ − 1) = ζ_{1/p}(3)` with the normalisation (1.1) of the manuscript.
The sum is indexed by `n + 1` so that the `n = 0` term (`0/0`) never appears. -/
noncomputable def xi (p : ℕ) : ℝ := ∑' n : ℕ, term p (n + 1)

/-! ### The algebraic data: moments, partial sums, the matrix and its determinant -/

/-- The polynomial moments `μ_j = j²/(p^j − 1)` for `j ≥ 1`, and `μ_0 = L(1) = 0` (eq. (1.4)). -/
def mu (p : ℕ) (j : ℕ) : ℚ := if j = 0 then 0 else (j : ℚ) ^ 2 / ((p : ℚ) ^ j - 1)

/-- The partial sums `S_a = ∑_{b=1}^a p^b (p^b + 1)/(p^b − 1)³` (eq. (1.5)). -/
def S (p : ℕ) (a : ℕ) : ℚ :=
  ∑ b ∈ Icc 1 a, ((p : ℚ) ^ b * ((p : ℚ) ^ b + 1)) / ((p : ℚ) ^ b - 1) ^ 3

/-- The linear functional `L` on polynomials, `L(∑ c_j x^j) = ∑ c_j μ_j` (eq. (1.4)). -/
def Lpoly (p : ℕ) (f : ℚ[X]) : ℚ := ∑ j ∈ f.support, f.coeff j * mu p j

/-- `F_K(x) = ∏_{a=1}^K (x − p^a)` (§3); `D_K = (−1)^K p^{−A_K} F_K`. -/
noncomputable def F (p K : ℕ) : ℚ[X] := ∏ a ∈ Icc 1 K, (X - C ((p : ℚ) ^ a))

/-- `A_K = K(K+1)/2` (eq. (1.8)). -/
def AK (K : ℕ) : ℕ := K * (K + 1) / 2

/-- `e_K = A_K (K−1) = K(K²−1)/2` (eq. (1.8)); defined through `AK` so that it is exact in `ℕ`. -/
def eK (K : ℕ) : ℕ := AK K * (K - 1)

/-- The residue coefficient `r_a^k / F_K'(r_a)` of `x^k/F_K` at the simple pole `r_a = p^a`. -/
noncomputable def res (p K k a : ℕ) : ℚ :=
  (p : ℚ) ^ (a * k) / (derivative (F p K)).eval ((p : ℚ) ^ a)

/-- Constant term (in the formal variable `X`) of `M_k(X) = L_X(x^k / F_K)`: the polynomial
moments of the quotient `x^k /ₘ F_K` plus `∑_a res_a S_a / p^a` (from
`L_X((x − r_a)⁻¹) = −(X − S_a)/r_a`). -/
noncomputable def mConst (p K k : ℕ) : ℚ :=
  Lpoly p (X ^ k /ₘ F p K) + ∑ a ∈ Icc 1 K, res p K k a * S p a / (p : ℚ) ^ a

/-- Coefficient of `X` in `M_k(X) = L_X(x^k / F_K)`: `−∑_a res_a / p^a`. -/
noncomputable def mLin (p K k : ℕ) : ℚ := -∑ a ∈ Icc 1 K, res p K k a / (p : ℚ) ^ a

/-- The normalisation `(−1)^K p^{A_K}` converting `1/F_K` into `1/D_K`. -/
def nrm (p K : ℕ) : ℚ := (-1) ^ K * (p : ℚ) ^ AK K

/-- The `X`-coefficient matrix of the Hankel matrix `[L_X(x^{i+j}/D_K)]`. -/
noncomputable def hankelLin (p K : ℕ) : Matrix (Fin K) (Fin K) ℚ :=
  Matrix.of fun i j => nrm p K * mLin p K (i.val + j.val)

/-- The constant-coefficient matrix of the Hankel matrix `[L_X(x^{i+j}/D_K)]`. -/
noncomputable def hankelConst (p K : ℕ) : Matrix (Fin K) (Fin K) ℚ :=
  Matrix.of fun i j => nrm p K * mConst p K (i.val + j.val)

/-- `Δ_K(X) = det [L_X(x^{i+j}/D_K)]_{0 ≤ i,j < K} ∈ ℚ[X]` (eq. (1.7)), written as the
determinant of `X • B + A` with `B = hankelLin`, `A = hankelConst`. -/
noncomputable def Delta (p K : ℕ) : ℚ[X] :=
  Matrix.det ((X : ℚ[X]) • (hankelLin p K).map C + (hankelConst p K).map C)

/-- `Δ_K` evaluated at a real number. -/
noncomputable def DeltaR (p K : ℕ) (x : ℝ) : ℝ := aeval x (Delta p K)

/-! ### Quantities of the real determinant bound (Proposition 2.1) -/

/-- `a_j = ∑_{t=1}^{j} ⌈t/3⌉`; for natural numbers `⌈t/3⌉ = (t + 2)/3`. -/
def aj (j : ℕ) : ℕ := ∑ t ∈ Icc 1 j, (t + 2) / 3

/-- `b_K = 2 ∑_{j<K} a_j = (K³ + 3K² − c_{K mod 3})/9`. -/
def bK (K : ℕ) : ℕ := 2 * ∑ j ∈ range K, aj j

/-! ### The cyclotomic multiplier (Proposition 4.1 and Appendix A) -/

/-- The exponent `c_{K,d}` of eq. (4.1): `⌈K²/(4d) + 2K + 17d/16⌉` for `d ≤ K/2` and
`7(K − d) + 3` for `K/2 < d ≤ K`. -/
def cMain (K d : ℕ) : ℕ :=
  if 2 * d ≤ K then ⌈(K : ℚ) ^ 2 / (4 * d) + 2 * K + 17 * d / 16⌉₊ else 7 * (K - d) + 3

/-- The stronger exponent of Appendix A: `5(K − d) + 3` in the high range. -/
def cApp (K d : ℕ) : ℕ :=
  if 2 * d ≤ K then ⌈(K : ℚ) ^ 2 / (4 * d) + 2 * K + 17 * d / 16⌉₊ else 5 * (K - d) + 3

/-- `Φ_d(p) ∈ ℤ`, the `d`-th cyclotomic polynomial evaluated at `p`. -/
noncomputable def Phi (p d : ℕ) : ℤ := (cyclotomic d ℤ).eval (p : ℤ)

/-- `C_K = ∏_{d=1}^{K} Φ_d(p)^{c_{K,d}}` with the Appendix A exponents (eq. (4.2)). -/
noncomputable def CK (p K : ℕ) : ℤ := ∏ d ∈ Icc 1 K, Phi p d ^ cApp K d

/-- The margin `ε = 11/18 − 321/(64π²)` of Appendix A (`≈ 0.1029`). -/
noncomputable def margin : ℝ := 11 / 18 - 321 / (64 * Real.pi ^ 2)

end QZeta3
