import QZeta3.Elementary
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
Integer row/column weights and determinant clearing over an arbitrary subring.
These are structural tools for the local denominator proof. They do not assert the
unproved cluster estimates for the actual q-zeta determinant.
-/
open Finset Matrix Polynomial
namespace QZeta3

/-- Integer row weight replacing the half-integer cluster weight. -/
def clusterRowWeight (m j : ℕ) : ℕ := max 1 ((m+3)/2-j)
/-- Complementary integer column weight. -/
def clusterColWeight (m j : ℕ) : ℕ := (m+2)/2-j

theorem cluster_weights_polynomial (m n i j : ℕ) :
    1 ≤ clusterRowWeight m i+clusterColWeight n j := by
  unfold clusterRowWeight clusterColWeight
  omega

theorem cluster_weights_proper (m i j : ℕ) :
    m+2 ≤ clusterRowWeight m i+clusterColWeight m j+i+j := by
  unfold clusterRowWeight clusterColWeight
  omega

theorem cluster_weights_cost (m j : ℕ) :
    clusterRowWeight m j+clusterColWeight m j=max 1 (m+2-2*j) := by
  unfold clusterRowWeight clusterColWeight
  omega

theorem sum_range_natCast (n : ℕ) : ∑ j ∈ range n, (j : ℝ) = n*((n : ℝ)-1)/2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The integer weights have precisely the same quadratic cost as the half-integer ones. -/
theorem sum_cluster_weights_le (m : ℕ) :
    (∑ j ∈ range m, ((clusterRowWeight m j+clusterColWeight m j : ℕ) : ℝ)) ≤
      (m : ℝ)^2/4+2*m+1 := by
  simp_rw [cluster_weights_cost]
  have he (j : ℕ) : max 1 (m+2-2*j)=1+(m+1-2*j) := by omega
  simp_rw [he, Nat.cast_add, Nat.cast_one, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_range, mul_one]
  let h := (m+2)/2
  have hsum : (∑ j ∈ range m, ((m+1-2*j : ℕ) : ℝ)) ≤
      ∑ j ∈ range h, ((m+1-2*j : ℕ) : ℝ) := by
    rcases le_total m h with hm | hm
    · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
      intro _ _ _; positivity
    · have heq : (∑ j ∈ range m, ((m+1-2*j : ℕ) : ℝ)) =
          ∑ j ∈ range h, ((m+1-2*j : ℕ) : ℝ) := by
        symm
        apply Finset.sum_subset (Finset.range_mono hm)
        intro j hj hj'
        simp only [Finset.mem_range] at hj hj'
        have : m+1-2*j=0 := by dsimp [h] at hj'; omega
        simp [this]
      exact heq.le
  have heq : (∑ j ∈ range h, ((m+1-2*j : ℕ) : ℝ)) =
      (h : ℝ)*((m : ℝ)+2-h) := by
    calc (∑ j ∈ range h, ((m+1-2*j : ℕ) : ℝ)) =
        ∑ j ∈ range h, ((m : ℝ)+1-2*j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hj' : 2*j≤m+1 := by have := Finset.mem_range.mp hj; dsimp [h] at this; omega
          push_cast [Nat.cast_sub hj']
          rfl
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum, sum_range_natCast]
        simp only [nsmul_eq_mul, Finset.card_range]
        ring
  rw [heq] at hsum
  nlinarith [sq_nonneg ((h : ℝ)-((m : ℝ)+2)/2)]

section Subring
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

theorem det_mem_subring (S : Subring R) (M : Matrix ι ι R)
    (hM : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  apply S.sum_mem
  intro σ _
  have hp : (∏ i, M (σ i) i) ∈ S := S.prod_mem (fun i _ => hM (σ i) i)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simpa [h] using hp
  · simpa [h] using S.neg_mem hp

/-- Entrywise row/column clearing clears the determinant by the sum of the weights. -/
theorem det_weighted_mem_subring (S : Subring R) (τ : R) (M : Matrix ι ι R)
    (r c : ι → ℕ) (hM : ∀ i j, τ^(r i+c j)*M i j ∈ S) :
    τ^((∑ i, r i)+(∑ j, c j))*M.det ∈ S := by
  let A : Matrix ι ι R := Matrix.of fun i j => τ^(r i+c j)*M i j
  have hdet : A.det = τ^((∑ i, r i)+(∑ j, c j))*M.det := by
    have hA : A = Matrix.of fun i j => τ^(r i)*(Matrix.of fun k l => τ^(c l)*M k l) i j := by
      ext i j
      simp only [A, Matrix.of_apply, pow_add]
      ring
    rw [hA, Matrix.det_mul_column, Matrix.det_mul_row,
      Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, pow_add]
    ring
  rw [← hdet]
  exact det_mem_subring S A hM

/-- Full row expansion, with the scalar extracted for the selected rows. -/
theorem det_add_smul_eq_sum (A B : Matrix ι ι R) (t : R) :
    (A+t • B).det=∑ s : Finset ι, t^s.card*Matrix.det (s.piecewise B A) := by
  have he := (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R).map_add_univ (t • B) A
  change (t • B+A).det = _ at he
  rw [add_comm] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro s _
  have hM : s.piecewise (t • B) A =
      fun i => (if i ∈ s then t else 1) • (s.piecewise B A) i := by
    funext i j
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  change Matrix.detRowAlternating _ = _
  rw [hM, AlternatingMap.map_smul_univ]
  simp only [smul_eq_mul]
  congr 1
  simp
end Subring

section Field
variable {R ι : Type*} [Field R] [Fintype ι] [DecidableEq ι]

/-- Selecting more rows from `B` than its rank forces the mixed determinant to vanish. -/
theorem det_piecewise_eq_zero_of_rank_lt (A B : Matrix ι ι R) (s : Finset ι)
    (hs : B.rank < s.card) : Matrix.det (s.piecewise B A)=0 := by
  classical
  by_contra hne
  have hli0 := (Matrix.linearIndependent_rows_of_det_ne_zero hne).comp
    (fun i : s => (i : ι)) Subtype.val_injective
  have hli : LinearIndependent R (fun i : s => B i) := by
    simpa [Function.comp_def, Finset.piecewise] using hli0
  have hspan : Submodule.span R (Set.range (fun i : s => B i)) ≤
      Submodule.span R (Set.range (fun i => B i)) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  have hdim := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli, Fintype.card_coe] at hdim
  have hrank : Module.finrank R (Submodule.span R (Set.range (fun i => B i))) = B.rank := by
    exact (Matrix.rank_eq_finrank_span_cols B.transpose).symm.trans (Matrix.rank_transpose B)
  rw [hrank] at hdim
  omega

/-- A pole of order one multiplying a rank-`r` integral matrix costs at most `r`
orders in the determinant. This is the polynomial-moment correction from the manuscript. -/
theorem pow_mul_det_add_inv_mem_subring (S : Subring R) (τ : R) (hτ : τ≠0) (hτS : τ∈S)
    (A B : Matrix ι ι R) (hA : ∀ i j, A i j∈S) (hB : ∀ i j, B i j∈S)
    (r : ℕ) (hr : B.rank≤r) : τ^r*(A+τ⁻¹ • B).det∈S := by
  rw [det_add_smul_eq_sum, Finset.mul_sum]
  apply S.sum_mem
  intro s _
  by_cases hs : s.card ≤ r
  · have he : τ^r*(τ⁻¹)^s.card=τ^(r-s.card) := by
      rw [inv_pow, ← div_eq_mul_inv]
      nth_rw 1 [← Nat.sub_add_cancel hs]
      rw [pow_add]
      field_simp
    rw [← mul_assoc, he]
    apply S.mul_mem (S.pow_mem hτS _)
    apply det_mem_subring
    intro i j
    by_cases hi : i∈s <;> simp only [Finset.piecewise, hi, ite_true, ite_false]
    · exact hB i j
    · exact hA i j
  · rw [det_piecewise_eq_zero_of_rank_lt A B s (by omega), mul_zero, mul_zero]
    exact S.zero_mem

/-- The rank correction also works coefficientwise in a formal target variable. -/
theorem det_piecewise_polynomial_eq_zero_of_rank_lt
    (A : Matrix ι ι R[X]) (B : Matrix ι ι R) (s : Finset ι)
    (hs : B.rank<s.card) : Matrix.det (s.piecewise (B.map Polynomial.C) A)=0 := by
  classical
  by_contra hne
  have hli0 := (Matrix.linearIndependent_rows_of_det_ne_zero hne).comp
    (fun i : s => (i : ι)) Subtype.val_injective
  have hliP : LinearIndependent R[X] (fun i : s => (B.map Polynomial.C) i) := by
    simpa [Function.comp_def, Finset.piecewise] using hli0
  have hliR := hliP.restrict_scalars' R
  let φ : (ι → R) →ₗ[R] (ι → R[X]) := LinearMap.pi
    (fun j => Polynomial.CAlgHom.toLinearMap.comp (LinearMap.proj j))
  have hli : LinearIndependent R (fun i : s => B i) := by
    apply LinearIndependent.of_comp φ
    exact hliR
  have hspan : Submodule.span R (Set.range (fun i : s => B i)) ≤
      Submodule.span R (Set.range (fun i => B i)) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  have hdim := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli, Fintype.card_coe] at hdim
  have hrank : Module.finrank R (Submodule.span R (Set.range (fun i => B i))) = B.rank :=
    (Matrix.rank_eq_finrank_span_cols B.transpose).symm.trans (Matrix.rank_transpose B)
  rw [hrank] at hdim
  omega

/-- Polynomial-valued version of the exact low-rank pole correction. The subring `T`
may be the polynomials whose coefficients are regular at a fixed cyclotomic root. -/
theorem C_pow_mul_det_add_inv_mem_subring (T : Subring R[X]) (τ : R) (hτ : τ≠0)
    (hτT : Polynomial.C τ∈T) (A : Matrix ι ι R[X]) (B : Matrix ι ι R)
    (hA : ∀ i j, A i j∈T) (hB : ∀ i j, Polynomial.C (B i j)∈T)
    (r : ℕ) (hr : B.rank≤r) :
    (Polynomial.C τ)^r*(A+(Polynomial.C τ⁻¹) • B.map Polynomial.C).det∈T := by
  rw [det_add_smul_eq_sum, Finset.mul_sum]
  apply T.sum_mem
  intro s _
  by_cases hs : s.card ≤ r
  · have he : (Polynomial.C τ)^r*(Polynomial.C τ⁻¹)^s.card=(Polynomial.C τ)^(r-s.card) := by
      rw [← map_pow, ← map_pow, ← map_mul, ← map_pow]
      congr 1
      rw [inv_pow, ← div_eq_mul_inv]
      nth_rw 1 [← Nat.sub_add_cancel hs]
      rw [pow_add]
      field_simp
    rw [← mul_assoc, he]
    apply T.mul_mem (T.pow_mem hτT _)
    apply det_mem_subring
    intro i j
    by_cases hi : i∈s <;> simp only [Finset.piecewise, hi, ite_true, ite_false]
    · exact hB i j
    · exact hA i j
  · rw [det_piecewise_polynomial_eq_zero_of_rank_lt A B s (by omega), mul_zero, mul_zero]
    exact T.zero_mem
end Field
end QZeta3
