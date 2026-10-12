import QZeta3.MovingClusterBasis
import Mathlib.Data.Int.CardIntervalMod

open Finset
namespace QZeta3.Generic

/-- The residue classes partition the moving nodes. -/
theorem sum_clusterMultiplicity {K d : ℕ} (hd : 0 < d) :
    ∑ r ∈ range d, clusterMultiplicity K d r = K := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Icc 1 K) (t := range d) (f := fun a : ℕ => a % d)
    (fun a _ => mem_range.mpr (Nat.mod_lt a hd))
  simpa [clusterMultiplicity, clusterIndices] using h.symm

/-- An exact residue count after shifting the interval to start at zero. -/
theorem clusterMultiplicity_formula {K d r : ℕ} (hd : 0 < d) (hr : r < d) :
    clusterMultiplicity K d r = K / d +
      if (r+d-1) % d < K % d then 1 else 0 := by
  let v := r+d-1
  have hv : v+1 ≡ r [MOD d] := by
    dsimp [v]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r+d)]
    exact Nat.add_modEq_right
  have he (a : ℕ) : a+1 ≡ r [MOD d] ↔ a ≡ v [MOD d] := by
    constructor
    · intro h
      exact (h.trans hv.symm).add_right_cancel' 1
    · intro h
      exact (h.add_right 1).trans hv
  have hc : clusterMultiplicity K d r = Nat.count (fun a => a ≡ v [MOD d]) K := by
    rw [Nat.count_eq_card_filter_range]
    unfold clusterMultiplicity
    symm
    apply Finset.card_bij (fun a _ => a+1)
    · intro a ha
      simp only [mem_filter, mem_range] at ha
      have hm : (a+1)%d=r := by
        have h := (he a).mpr ha.2
        simpa [Nat.ModEq, Nat.mod_eq_of_lt hr] using h
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hm⟩
    · intro a ha b hb hab
      omega
    · intro b hb
      have hb' : 1 ≤ b ∧ b ≤ K ∧ b%d=r := by
        simpa only [clusterIndices, mem_filter, mem_Icc, and_assoc] using hb
      refine ⟨b-1, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, by omega⟩
      apply (he (b-1)).mp
      have hb1 : b-1+1=b := by omega
      simpa [hb1, Nat.ModEq, Nat.mod_eq_of_lt hr] using hb'.2.2
  rw [hc, Nat.count_modEq_card K hd v]

/-- Every residue class has one of two consecutive cardinalities. -/
theorem clusterMultiplicity_balanced {K d r : ℕ} (hd : 0 < d) (hr : r < d) :
    clusterMultiplicity K d r = K/d ∨ clusterMultiplicity K d r = K/d+1 := by
  rw [clusterMultiplicity_formula hd hr]
  split_ifs <;> omega

/-- Exact second-moment identity for the balanced residue classes. -/
theorem sum_sq_clusterMultiplicity {K d : ℕ} (hd : 0 < d) :
    (∑ r ∈ range d, (clusterMultiplicity K d r : ℝ)^2) =
      (2*(K/d : ℕ)+1 : ℝ)*K - d*(K/d : ℕ)*((K/d : ℕ)+1) := by
  have he (r : ℕ) (hr : r ∈ range d) :
      (clusterMultiplicity K d r : ℝ)^2 =
        (2*(K/d : ℕ)+1 : ℝ)*clusterMultiplicity K d r -
          (K/d : ℕ)*((K/d : ℕ)+1) := by
    rcases clusterMultiplicity_balanced hd (mem_range.mp hr) with h | h
    · rw [h]; ring
    · rw [h]; push_cast; ring
  rw [Finset.sum_congr rfl he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsum : (∑ r ∈ range d, (clusterMultiplicity K d r : ℝ)) = K := by
    exact_mod_cast sum_clusterMultiplicity (K := K) hd
  rw [hsum, Finset.sum_const]
  simp only [Finset.card_range, nsmul_eq_mul]
  ring

/-- The variance of equally spaced residue classes costs at most `d/4`. -/
theorem sum_sq_clusterMultiplicity_le {K d : ℕ} (hd : 0 < d) :
    (∑ r ∈ range d, (clusterMultiplicity K d r : ℝ)^2) ≤
      (K : ℝ)^2/d + d/4 := by
  rw [sum_sq_clusterMultiplicity hd]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  apply (mul_le_mul_iff_left₀ hdR).mp
  have hc : ((K : ℝ)^2/d + d/4)*d = (K : ℝ)^2 + (d : ℝ)^2/4 := by
    field_simp
  rw [hc]
  nlinarith [sq_nonneg ((K : ℝ) - d*((K/d : ℕ)+1/2 : ℝ))]

/-- Total integer row/column clearing cost, before taking a ceiling. -/
theorem sum_cluster_weights_bound {K d : ℕ} (hd : 0 < d) :
    (∑ r ∈ range d, ∑ j ∈ range (clusterMultiplicity K d r),
      ((clusterRowWeight (clusterMultiplicity K d r) j +
        clusterColWeight (clusterMultiplicity K d r) j : ℕ) : ℝ)) ≤
      (K : ℝ)^2/(4*d) + 2*K + 17*d/16 := by
  have h := Finset.sum_le_sum (s := range d) (fun r _ =>
    sum_cluster_weights_le (clusterMultiplicity K d r))
  have hsum : (∑ r ∈ range d, (clusterMultiplicity K d r : ℝ)) = K := by
    exact_mod_cast sum_clusterMultiplicity (K := K) hd
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
  rw [hsum] at h
  have hs := sum_sq_clusterMultiplicity_le (K := K) hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he : (K : ℝ)^2/(4*d) = ((K : ℝ)^2/d)/4 := by ring
  rw [he]
  linarith

/-- The low-range cyclotomic exponent dominates the full cluster weight sum. -/
theorem sum_cluster_weights_le_cApp {K d : ℕ} (hd : 0 < d) (hlo : 2*d ≤ K) :
    (∑ r ∈ range d, ∑ j ∈ range (clusterMultiplicity K d r),
      (clusterRowWeight (clusterMultiplicity K d r) j +
        clusterColWeight (clusterMultiplicity K d r) j)) ≤ cApp K d := by
  have h := sum_cluster_weights_bound (K := K) hd
  unfold cApp
  simp only [hlo, ite_true]
  have hceil : (K : ℚ)^2/(4*d) + 2*K + 17*d/16 ≤
      (⌈(K : ℚ)^2/(4*d) + 2*K + 17*d/16⌉₊ : ℚ) := Nat.le_ceil _
  have hceilR : (K : ℝ)^2/(4*d) + 2*K + 17*d/16 ≤
      (⌈(K : ℚ)^2/(4*d) + 2*K + 17*d/16⌉₊ : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hceil
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_ofNat] using hc
  have hfinal := h.trans hceilR
  exact_mod_cast hfinal

theorem sum_clusterMultiplicity_fin {K d : ℕ} (hd : 0 < d) :
    ∑ r : Fin d, clusterMultiplicity K d r = K := by
  rw [Finset.sum_fin_eq_sum_range]
  calc (∑ r ∈ range d, if h : r<d then clusterMultiplicity K d r else 0) =
      ∑ r ∈ range d, clusterMultiplicity K d r := by
        apply Finset.sum_congr rfl
        intro r hr
        simp [mem_range.mp hr]
    _ = K := sum_clusterMultiplicity hd

theorem clusterMultiplicity_high {K d r : ℕ} (hd : 0 < d) (hdK : d ≤ K)
    (hKd : K < 2*d) (hr : r < d) :
    clusterMultiplicity K d r = 1 + if 0<r ∧ r≤K-d then 1 else 0 := by
  have hdiv : K/d=1 := Nat.div_eq_of_lt_le (by simpa using hdK) (by simpa using hKd)
  have hmod : K%d=K-d := by rw [Nat.mod_eq_sub, hdiv, mul_one]
  rw [clusterMultiplicity_formula hd hr, hdiv, hmod]
  congr 1
  by_cases hr0 : r=0
  · subst r
    simp only [zero_add, Nat.mod_eq_of_lt (by omega : d-1<d)]
    have hn : ¬d-1<K-d := by omega
    simp [hn]
  · have he : r+d-1=(r-1)+d := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : r-1<d)]
    split_ifs <;> omega

/-- In the high range, every cluster is a singleton or one explicit pair. -/
theorem mem_clusterIndices_high {K d r a : ℕ} (hd : 0 < d) (hdK : d ≤ K)
    (hKd : K < 2*d) (hr : r < d) :
    a ∈ clusterIndices K d r ↔
      (a=r ∧ 0<r) ∨ (a=r+d ∧ r≤K-d) := by
  simp only [clusterIndices, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨ha1, haK⟩, hamod⟩
    by_cases had : a<d
    · rw [Nat.mod_eq_of_lt had] at hamod
      exact Or.inl ⟨hamod, by omega⟩
    · have had' : d≤a := by omega
      rw [Nat.mod_eq_sub_mod had', Nat.mod_eq_of_lt (by omega : a-d<d)] at hamod
      exact Or.inr ⟨by omega, by omega⟩
  · rintro (⟨rfl, hr0⟩ | ⟨rfl, hrK⟩)
    · exact ⟨⟨by omega, by omega⟩, Nat.mod_eq_of_lt hr⟩
    · exact ⟨⟨by omega, by omega⟩, by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hr]⟩

theorem clusterIndices_high_zero {K d : ℕ} (hd : 0 < d) (hdK : d ≤ K)
    (hKd : K < 2*d) : clusterIndices K d 0 = {d} := by
  ext a
  rw [mem_clusterIndices_high hd hdK hKd hd]
  simp

theorem clusterIndices_high_pair {K d r : ℕ} (hd : 0 < d) (hdK : d ≤ K)
    (hKd : K < 2*d) (hr : r < d) (hr0 : 0 < r) (hrK : r ≤ K-d) :
    clusterIndices K d r = {r,r+d} := by
  ext a
  rw [mem_clusterIndices_high hd hdK hKd hr]
  simp [hr0, hrK]

theorem clusterIndices_high_singleton {K d r : ℕ} (hd : 0 < d) (hdK : d ≤ K)
    (hKd : K < 2*d) (hr : r < d) (hrK : K-d < r) :
    clusterIndices K d r = {r} := by
  ext a
  rw [mem_clusterIndices_high hd hdK hKd hr]
  simp [show 0<r by omega, show ¬r≤K-d by omega]

/-- Exactly the residues `1,…,K-d` have two moving nodes in the high range. -/
theorem clusterMultiplicity_two_residues {K d : ℕ} (hd : 0 < d) (hdK : d ≤ K)
    (hKd : K < 2*d) :
    (range d).filter (fun r => clusterMultiplicity K d r = 2) = Icc 1 (K-d) := by
  ext r
  simp only [mem_filter, mem_range, mem_Icc]
  constructor
  · rintro ⟨hr, hm⟩
    rw [clusterMultiplicity_high hd hdK hKd hr] at hm
    split_ifs at hm with h
    · exact ⟨h.1, h.2⟩
    · omega
  · rintro ⟨hr1, hrK⟩
    have hr : r<d := by omega
    exact ⟨hr, by rw [clusterMultiplicity_high hd hdK hKd hr]; simp [show 0<r by omega, hrK]⟩

theorem card_clusterMultiplicity_two {K d : ℕ} (hd : 0 < d) (hdK : d ≤ K)
    (hKd : K < 2*d) :
    ((range d).filter (fun r => clusterMultiplicity K d r = 2)).card = K-d := by
  rw [clusterMultiplicity_two_residues hd hdK hKd]
  simp

/-- The clearing bound in the sigma-indexed form used by the cluster basis. -/
theorem sum_cluster_weights_sigma_le_cApp {K d : ℕ} (hd : 0 < d) (hlo : 2*d ≤ K) :
    (∑ i : (Σ r : Fin d, Fin (clusterMultiplicity K d r)),
      (clusterRowWeight (clusterMultiplicity K d i.1) i.2 +
        clusterColWeight (clusterMultiplicity K d i.1) i.2)) ≤ cApp K d := by
  rw [Fintype.sum_sigma]
  have hi (r : Fin d) :
      (∑ j : Fin (clusterMultiplicity K d r),
        (clusterRowWeight (clusterMultiplicity K d r) j +
        clusterColWeight (clusterMultiplicity K d r) j)) =
      ∑ j ∈ range (clusterMultiplicity K d r),
        (clusterRowWeight (clusterMultiplicity K d r) j +
        clusterColWeight (clusterMultiplicity K d r) j) :=
    Fin.sum_univ_eq_sum_range
      (fun j => clusterRowWeight (clusterMultiplicity K d r) j +
        clusterColWeight (clusterMultiplicity K d r) j) (clusterMultiplicity K d r)
  simp_rw [hi]
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ =>
    ∑ j ∈ range (clusterMultiplicity K d r),
      (clusterRowWeight (clusterMultiplicity K d r) j +
        clusterColWeight (clusterMultiplicity K d r) j)) d]
  exact sum_cluster_weights_le_cApp hd hlo

end QZeta3.Generic
