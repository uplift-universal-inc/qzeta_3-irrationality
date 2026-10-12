import QZeta3.LocalDeterminants

/-! Polynomial cluster independence by the Chinese remainder argument. -/
open Polynomial Finset
namespace QZeta3
section Cluster
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]

noncomputable def clusterFactor (a : ι → k) (m : ι → ℕ) (r : ι) : k[X] :=
  (X-C (a r))^(m r)
noncomputable def clusterComplement (a : ι → k) (m : ι → ℕ) (r : ι) : k[X] :=
  ∏ s ∈ univ.erase r, clusterFactor a m s

theorem clusterFactor_coprime_complement (a : ι → k) (ha : Function.Injective a)
    (m : ι → ℕ) (r : ι) : IsCoprime (clusterFactor a m r) (clusterComplement a m r) := by
  unfold clusterComplement
  apply IsCoprime.prod_right
  intro s hs
  have hrs : a r ≠ a s := fun h => (Finset.mem_erase.mp hs).1 (ha h).symm
  exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hrs).isUnit).pow

theorem clusterFactor_dvd_complement (a : ι → k) (m : ι → ℕ) {r s : ι} (hrs : r≠s) :
    clusterFactor a m r ∣ clusterComplement a m s := by
  exact Finset.dvd_prod_of_mem _ (by simp [hrs])

/-- The independent cluster summands: reduction modulo one cluster factor isolates its summand. -/
theorem cluster_sum_injective (a : ι → k) (ha : Function.Injective a) (m : ι → ℕ)
    (Q : ι → k[X]) (hQ : ∀ r, (Q r).natDegree<m r)
    (hsum : ∑ r, clusterComplement a m r*Q r=0) : ∀ r, Q r=0 := by
  intro r
  have hdvd : clusterFactor a m r ∣
      ∑ s ∈ univ.erase r, clusterComplement a m s*Q s := by
    apply Finset.dvd_sum
    intro s hs
    exact dvd_mul_of_dvd_left (clusterFactor_dvd_complement a m (Finset.mem_erase.mp hs).1.symm) _
  have he := Finset.sum_erase_add univ (fun s => clusterComplement a m s*Q s) (mem_univ r)
  rw [hsum] at he
  have heq : clusterComplement a m r*Q r = -(∑ s ∈ univ.erase r, clusterComplement a m s*Q s) := by
    linear_combination he
  have hterm : clusterFactor a m r ∣ clusterComplement a m r*Q r := by
    rw [heq]
    exact dvd_neg.mpr hdvd
  have hdiv := (clusterFactor_coprime_complement a ha m r).dvd_of_dvd_mul_left hterm
  apply Polynomial.eq_zero_of_dvd_of_natDegree_lt hdiv
  simpa [clusterFactor] using hQ r

noncomputable def clusterCombination (a : k) (n : ℕ) (c : Fin n → k) : k[X] :=
  ∑ j, C (c j)*(X-C a)^j.val

theorem clusterCombination_degree (a : k) (n : ℕ) (hn : 0<n) (c : Fin n → k) :
    (clusterCombination a n c).natDegree<n := by
  have h : (clusterCombination a n c).natDegree≤n-1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    calc (C (c j)*(X-C a)^j.val).natDegree ≤ ((X-C a)^j.val).natDegree := natDegree_C_mul_le _ _
      _ = j.val := by simp
      _ ≤ n-1 := by have := j.isLt; omega
  omega

theorem clusterCombination_zero (a : k) (n : ℕ) (c : Fin n → k)
    (h : clusterCombination a n c=0) : ∀ j, c j=0 := by
  intro j
  have hc := congrArg (fun P : k[X] => (P.comp (X+C a)).coeff j.val) h
  simp only [clusterCombination, Polynomial.sum_comp, mul_comp, pow_comp, sub_comp,
    X_comp, C_comp, add_sub_cancel_right, finsetSum_coeff, zero_comp, coeff_zero,
    coeff_C_mul_X_pow] at hc
  simpa [Fin.val_inj] using hc

noncomputable def clusterBasis (a : ι → k) (m : ι → ℕ) (i : Σ r, Fin (m r)) : k[X] :=
  clusterComplement a m i.1*(X-C (a i.1))^i.2.val

/-- The reduction of the cluster basis is linearly independent; hence its coordinate
matrix has nonzero determinant once its dimension is identified with the total degree. -/
theorem clusterBasis_linearIndependent (a : ι → k) (ha : Function.Injective a)
    (m : ι → ℕ) (hm : ∀ r, 0<m r) : LinearIndependent k (clusterBasis a m) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hs : ∑ r, clusterComplement a m r * clusterCombination (a r) (m r) (fun j => c ⟨r,j⟩)=0 := by
    simpa only [clusterBasis, clusterCombination, Fintype.sum_sigma, Polynomial.smul_eq_C_mul,
      Finset.mul_sum, mul_left_comm, mul_assoc] using hc
  have hz := cluster_sum_injective a ha m
    (fun r => clusterCombination (a r) (m r) (fun j => c ⟨r,j⟩))
    (fun r => clusterCombination_degree (a r) (m r) (hm r) _) hs
  exact clusterCombination_zero (a i.1) (m i.1) _ (hz i.1) i.2

theorem clusterBasis_natDegree_lt (a : ι → k) (m : ι → ℕ) (i : Σ r, Fin (m r)) :
    (clusterBasis a m i).natDegree < ∑ r, m r := by
  have hdeg : (clusterComplement a m i.1).natDegree = ∑ r ∈ univ.erase i.1, m r := by
    unfold clusterComplement clusterFactor
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun r _ => (monic_X_sub_C (a r)).pow (m r))]
    simp [clusterFactor]
  have he := Finset.sum_erase_add univ m (mem_univ i.1)
  unfold clusterBasis
  have h : (clusterComplement a m i.1 * ((X-C (a i.1))^i.2.val)).natDegree ≤
      (clusterComplement a m i.1).natDegree+((X-C (a i.1))^i.2.val).natDegree := Polynomial.natDegree_mul_le
  rw [hdeg] at h
  simp only [Polynomial.natDegree_pow, natDegree_X_sub_C, mul_one] at h
  have hi := i.2.isLt
  omega

/-- A full family of independent polynomials of degree below `N` has an invertible
coefficient matrix. This supplies the matrix form of the cluster-basis argument. -/
theorem coeffMatrix_det_ne_zero {N : ℕ} (P : Fin N → k[X])
    (hdeg : ∀ i, (P i).natDegree<N) (hli : LinearIndependent k P) :
    (Matrix.of fun i j : Fin N => (P i).coeff j.val).det≠0 := by
  have hrows : LinearIndependent k (fun i : Fin N => fun j : Fin N => (P i).coeff j.val) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    apply (Fintype.linearIndependent_iff.mp hli) c
    ext n
    simp only [finsetSum_coeff, coeff_smul, coeff_zero]
    by_cases hn : n<N
    · have he := congrArg (fun v : Fin N → k => v ⟨n,hn⟩) hc
      simpa using he
    · apply Finset.sum_eq_zero
      intro i _
      rw [coeff_eq_zero_of_natDegree_lt ((hdeg i).trans_le (by omega)), smul_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

noncomputable def clusterBasisMatrix (a : ι → k) (m : ι → ℕ) :
    Matrix (Fin (Fintype.card (Σ r, Fin (m r)))) (Fin (Fintype.card (Σ r, Fin (m r)))) k :=
  Matrix.of fun i j => (clusterBasis a m ((Fintype.equivFin (Σ r, Fin (m r))).symm i)).coeff j.val

theorem clusterBasisMatrix_det_ne_zero (a : ι → k) (ha : Function.Injective a)
    (m : ι → ℕ) (hm : ∀ r, 0<m r) : (clusterBasisMatrix a m).det≠0 := by
  apply coeffMatrix_det_ne_zero
  · intro i
    simpa only [Fintype.card_sigma, Fintype.card_fin] using
      clusterBasis_natDegree_lt a m ((Fintype.equivFin (Σ r, Fin (m r))).symm i)
  · exact (clusterBasis_linearIndependent a ha m hm).comp _ (Equiv.injective _)
end Cluster
end QZeta3
