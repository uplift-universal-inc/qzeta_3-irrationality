import QZeta3.ClusterCounts
import QZeta3.HighOrderLocal

open Polynomial Finset

namespace QZeta3.Generic

variable {k : Type*} [Field k]

noncomputable def highClusterCenter (ω : k) (d : ℕ) (r : Fin d) : regularAt ω :=
  localBase ω ^ (r.val+d)

@[simp] theorem localEval_highClusterCenter {ω : k} {d : ℕ} (hω : ω^d=1) (r : Fin d) :
    localEval ω (highClusterCenter ω d r)=ω^r.val := by
  rw [highClusterCenter, _root_.map_pow, localEval_localBase, pow_add, hω, mul_one]

noncomputable def highClusterPoly (ω : k) (K d : ℕ) (i : ClusterIndex K d) :
    (regularAt ω)[X] := localClusterPoly ω K d (highClusterCenter ω d) i

noncomputable def highClusterMatrix (ω : k) (K d : ℕ) :=
  localClusterMatrix ω K d (highClusterCenter ω d)

theorem highClusterMatrix_det_isUnit {ω : k} {K d : ℕ} (hω : IsPrimitiveRoot ω d)
    (hd : 0<d) (hdK : d≤K) : IsUnit (highClusterMatrix ω K d).det :=
  localClusterMatrix_det_isUnit hω hd hdK (highClusterCenter ω d)
    (localEval_highClusterCenter hω.pow_eq_one)

theorem highClusterPoly_reduction {ω : k} {K d : ℕ} (hω : ω^d=1)
    (hd : 0<d) (i : ClusterIndex K d) :
    (highClusterPoly ω K d i).map (localEval ω) =
      QZeta3.clusterBasis (fun r : Fin d => ω^r.val)
        (fun r : Fin d => clusterMultiplicity K d r.val) i :=
  map_localClusterPoly ω K d hd hω (highClusterCenter ω d) (localEval_highClusterCenter hω) i

theorem highClusterPoly_subtype (ω : k) (K d : ℕ) (i : ClusterIndex K d) :
    (highClusterPoly ω K d i).map (regularAt ω).subtype =
      movingClusterComplement (RatFunc.X : RatFunc k) K d i.1.val *
        (X-C (RatFunc.X^(i.1.val+d)))^i.2.val := by
  simp [highClusterPoly, localClusterPoly, highClusterCenter, movingClusterComplement,
    localBase, Polynomial.map_prod]

theorem clusterMultiplicity_high_cases {K d r : ℕ} (hd : 0<d) (hdK : d≤K)
    (hhi : K<2*d) (hr : r<d) :
    clusterMultiplicity K d r=1 ∨ clusterMultiplicity K d r=2 := by
  rw [clusterMultiplicity_high hd hdK hhi hr]
  split_ifs <;> omega

theorem clusterMultiplicity_zero_high {K d : ℕ} (hd : 0<d) (hdK : d≤K)
    (hhi : K<2*d) : clusterMultiplicity K d 0=1 := by
  simpa using clusterMultiplicity_high hd hdK hhi hd

/-- Integer weights for the refined double-cluster basis. -/
def highRowWeight (K d : ℕ) (i : ClusterIndex K d) : ℕ :=
  (2*(clusterMultiplicity K d i.1.val-1)+(if i.1.val=0 then 2 else 0))*(1-i.2.val)
def highColWeight (K d : ℕ) (i : ClusterIndex K d) : ℕ :=
  (2*(clusterMultiplicity K d i.1.val-1)+(if i.1.val=0 then 1 else 0))*(1-i.2.val)

theorem high_weights_second {K d : ℕ} (i : ClusterIndex K d) (hi : 0 < i.2.val) :
    highRowWeight K d i=0 ∧ highColWeight K d i=0 := by
  have hj : 1-i.2.val=0 := by omega
  simp [highRowWeight, highColWeight, hj]

theorem high_weights_double {K d : ℕ} (hd : 0<d) (hdK : d≤K) (hhi : K<2*d)
    (i : ClusterIndex K d) (hm : clusterMultiplicity K d i.1.val=2) :
    highRowWeight K d i=2*(1-i.2.val) ∧ highColWeight K d i=2*(1-i.2.val) := by
  have hr : i.1.val ≠ 0 := by
    intro h
    rw [h, clusterMultiplicity_zero_high hd hdK hhi] at hm
    omega
  simp [highRowWeight, highColWeight, hm, hr]

theorem high_weights_zero {K d : ℕ} (hd : 0<d) (hdK : d≤K) (hhi : K<2*d)
    (i : ClusterIndex K d) (hi : i.1.val=0) :
    highRowWeight K d i=2 ∧ highColWeight K d i=1 := by
  have hm : clusterMultiplicity K d i.1.val=1 := hi ▸ clusterMultiplicity_zero_high hd hdK hhi
  have hj : i.2.val=0 := by have := i.2.isLt; omega
  simp [highRowWeight, highColWeight, hi, hj, clusterMultiplicity_zero_high hd hdK hhi]

theorem high_weights_singleton {K d : ℕ} (i : ClusterIndex K d)
    (hm : clusterMultiplicity K d i.1.val=1) (hi : i.1.val≠0) :
    highRowWeight K d i=0 ∧ highColWeight K d i=0 := by
  simp [highRowWeight, highColWeight, hm, hi]

private theorem sum_first_weight (m c : ℕ) (hm : 0<m) :
    (∑ j : Fin m, c*(1-j.val))=c := by
  rw [Finset.sum_eq_single (⟨0,hm⟩ : Fin m)]
  · simp
  · intro j hj hj0
    have hj : j.val≠0 := by simpa [Fin.ext_iff] using hj0
    have : 1-j.val=0 := by omega
    simp [this]
  · simp

theorem sum_high_weights {K d : ℕ} (hd : 0<d) (hdK : d≤K) :
    (∑ i : ClusterIndex K d, highRowWeight K d i) +
      (∑ i : ClusterIndex K d, highColWeight K d i) = 4*(K-d)+3 := by
  have hm (r : Fin d) : 0<clusterMultiplicity K d r.val :=
    clusterMultiplicity_pos K d hd hdK r.val r.isLt
  have hsum : (∑ r : Fin d, clusterMultiplicity K d r.val)=K := by
    rw [Fin.sum_univ_eq_sum_range]
    exact sum_clusterMultiplicity hd
  have hsub : (∑ r : Fin d, (clusterMultiplicity K d r.val-1))=K-d := by
    rw [Finset.sum_tsub_distrib]
    · simp [hsum]
    · intro r hr
      exact hm r
  have hzero (c : ℕ) : (∑ r : Fin d, if r.val=0 then c else 0)=c := by
    rw [Finset.sum_eq_single (⟨0,hd⟩ : Fin d)]
    · simp
    · intro r hr hr0
      have : r.val≠0 := by simpa [Fin.ext_iff] using hr0
      simp [this]
    · simp
  have hs (c : ℕ) : (∑ r : Fin d, ∑ j : Fin (clusterMultiplicity K d r.val),
      (2*(clusterMultiplicity K d r.val-1)+(if r.val=0 then c else 0))*(1-j.val)) =
      2*(K-d)+c := by
    calc _ = ∑ r : Fin d, (2*(clusterMultiplicity K d r.val-1)+(if r.val=0 then c else 0)) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact sum_first_weight _ _ (hm r)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsub, hzero]
  simp only [highRowWeight, highColWeight, Fintype.sum_sigma]
  rw [hs 2, hs 1]
  omega

theorem sum_high_weights_le_cApp {K d : ℕ} (hd : 0<d) (hdK : d≤K) (hhi : K<2*d) :
    (∑ i : ClusterIndex K d, highRowWeight K d i) +
      (∑ i : ClusterIndex K d, highColWeight K d i) ≤ cApp K d := by
  rw [sum_high_weights hd hdK]
  simp only [cApp, ite_eq_right (by omega : ¬2*d≤K)]
  omega

/-- The polynomial-moment correction fits in the remaining `K-d` pole orders. -/
theorem sum_high_weights_add_rank_le_cApp {K d r : ℕ} (hd : 0<d)
    (hdK : d≤K) (hhi : K<2*d) (hr : r≤K-d) :
    (∑ i : ClusterIndex K d, highRowWeight K d i) +
      (∑ i : ClusterIndex K d, highColWeight K d i) + r ≤ cApp K d := by
  rw [sum_high_weights hd hdK]
  simp only [cApp, ite_eq_right (by omega : ¬2*d≤K)]
  omega

end QZeta3.Generic
