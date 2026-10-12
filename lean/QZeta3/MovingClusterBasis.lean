import QZeta3.GenericMoments
import QZeta3.ClusterBasis
import QZeta3.CyclotomicLocal
import QZeta3.LocalEvaluation

/-! Cluster polynomials at the moving geometric nodes and their reduction. -/
open Polynomial Finset
namespace QZeta3.Generic

def clusterIndices (K d r : ℕ) : Finset ℕ := (Icc 1 K).filter (fun a => a%d=r)
def clusterMultiplicity (K d r : ℕ) : ℕ := (clusterIndices K d r).card

variable {k : Type*}

noncomputable def movingClusterComplement [CommRing k] (z : k) (K d r : ℕ) : k[X] :=
  ∏ a ∈ (Icc 1 K).filter (fun a => a%d≠r), (X-C (z^a))
noncomputable def movingClusterPoly [CommRing k] (z ω : k) (K d r j : ℕ) : k[X] :=
  movingClusterComplement z K d r*(X-C (ω^r))^j

variable [Field k]

theorem primitive_pow_eq_iff_mod_eq {ω : k} {d : ℕ} (hω : IsPrimitiveRoot ω d)
    (hd : 0<d) (a b : ℕ) : ω^a=ω^b ↔ a%d=b%d := by
  rw [pow_eq_pow_mod a hω.pow_eq_one, pow_eq_pow_mod b hω.pow_eq_one]
  exact ⟨hω.pow_inj (Nat.mod_lt a hd) (Nat.mod_lt b hd), fun h => congrArg (ω^·) h⟩

theorem clusterIndices_nonempty (K d : ℕ) (hd : 0<d) (hdK : d≤K) (r : ℕ) (hr : r<d) :
    (clusterIndices K d r).Nonempty := by
  by_cases hr0 : r=0
  · refine ⟨d, ?_⟩
    simp [clusterIndices, hr0, hdK]; omega
  · refine ⟨r, ?_⟩
    simp only [clusterIndices, mem_filter, mem_Icc]
    exact ⟨⟨by omega, by omega⟩, Nat.mod_eq_of_lt hr⟩

theorem clusterMultiplicity_pos (K d : ℕ) (hd : 0<d) (hdK : d≤K) (r : ℕ) (hr : r<d) :
    0<clusterMultiplicity K d r := Finset.card_pos.mpr (clusterIndices_nonempty K d hd hdK r hr)

theorem collisionCount_eq_clusterMultiplicity_sub_one {ω : k} {d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 0<d) (K a : ℕ) (ha : a∈Icc 1 K) :
    collisionCount ω K a=clusterMultiplicity K d (a%d)-1 := by
  classical
  have hset : ((Icc 1 K).erase a).filter (fun b => ω^a=ω^b) =
      (clusterIndices K d (a%d)).erase a := by
    ext b
    simp only [mem_filter, mem_erase, clusterIndices,
      primitive_pow_eq_iff_mod_eq hω hd]
    tauto
  unfold collisionCount clusterMultiplicity
  rw [hset, card_erase_of_mem]
  simp [clusterIndices, ha]

theorem movingClusterComplement_monic (z : k) (K d r : ℕ) :
    (movingClusterComplement z K d r).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem movingClusterComplement_coeff_mem (S : Subring k) (z : k) (hz : z∈S)
    (K d r i : ℕ) : (movingClusterComplement z K d r).coeff i∈S := by
  let P : S[X] := ∏ a ∈ (Icc 1 K).filter (fun a => a%d≠r),
    (X-C ((⟨z,hz⟩ : S)^a))
  have hmap : P.map S.subtype=movingClusterComplement z K d r := by
    simp [P, movingClusterComplement, Polynomial.map_prod]
  rw [← hmap, Polynomial.coeff_map]
  exact (P.coeff i).property

theorem movingClusterPoly_coeff_mem (S : Subring k) (z ω : k) (hz : z∈S) (hω : ω∈S)
    (K d r j i : ℕ) : (movingClusterPoly z ω K d r j).coeff i∈S := by
  let T := Polynomial.liftsRing S.subtype
  have hcomp : movingClusterComplement z K d r∈T :=
    (coeff_mem_iff_lifts S _).mp (movingClusterComplement_coeff_mem S z hz K d r)
  have hroot : (X-C (ω^r) : k[X])∈T := by
    apply (coeff_mem_iff_lifts S _).mp
    intro i
    rw [Polynomial.coeff_sub]
    apply S.sub_mem
    · simp only [coeff_X]; split_ifs <;> simp
    · simp only [coeff_C]; split_ifs <;> first | exact S.pow_mem hω r | exact S.zero_mem
  exact (coeff_mem_iff_lifts S _).mpr (T.mul_mem hcomp (T.pow_mem hroot j)) i

theorem movingClusterComplement_reduction (ω : k) (K d : ℕ) (hd : 0<d)
    (hω : ω^d=1) (r : Fin d) :
    movingClusterComplement ω K d r.val =
      QZeta3.clusterComplement (fun s : Fin d => ω^s.val)
        (fun s : Fin d => clusterMultiplicity K d s.val) r := by
  classical
  let g : ℕ → Fin d := fun a => ⟨a%d, Nat.mod_lt a hd⟩
  let s := (Icc 1 K).filter (fun a => a%d≠r.val)
  have hfiber (t : Fin d) : s.filter (fun a => g a=t) =
      if t=r then ∅ else clusterIndices K d t.val := by
    by_cases h : t=r
    · subst t
      ext a
      simp [s, g, Fin.ext_iff]
    · rw [ite_eq_right h]
      ext a
      simp only [s, clusterIndices, mem_filter, g, Fin.ext_iff]
      constructor
      · intro ha
        exact ⟨ha.1.1, ha.2⟩
      · intro ha
        exact ⟨⟨ha.1, fun he => h (Fin.ext (ha.2.symm.trans he))⟩, ha.2⟩

  have hprod (t : Fin d) : (∏ a ∈ s.filter (fun a => g a=t), (X-C (ω^a))) =
      if t=r then 1 else (X-C (ω^t.val))^(clusterMultiplicity K d t.val) := by
    rw [hfiber]
    split_ifs with h
    · simp
    · calc (∏ a ∈ clusterIndices K d t.val, (X-C (ω^a))) =
          ∏ a ∈ clusterIndices K d t.val, (X-C (ω^t.val)) := by
            apply Finset.prod_congr rfl
            intro a ha
            rw [pow_eq_pow_mod a hω, (Finset.mem_filter.mp ha).2]
        _ = _ := by simp [clusterMultiplicity]
  change (∏ a ∈ s, (X-C (ω^a))) = _
  rw [← Finset.prod_fiberwise s g (fun a => (X-C (ω^a)))]
  simp_rw [hprod]
  unfold QZeta3.clusterComplement QZeta3.clusterFactor
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul]
  congr 1
  ext t
  simp [ne_comm]

/-- The geometric base as an element of the local ring. -/
noncomputable def localBase (ω : k) : regularAt ω := ⟨RatFunc.X, base_mem_regularAt ω⟩

@[simp] theorem localEval_localBase (ω : k) : localEval ω (localBase ω)=ω := by
  simp [localBase]

/-- Cluster indices, retaining every polynomial in each residue class. -/
abbrev ClusterIndex (K d : ℕ) := Σ r : Fin d, Fin (clusterMultiplicity K d r.val)

/-- A cluster basis with arbitrary lifted centers. The high-order range uses moving
upper nodes as centers; only their reductions are relevant to invertibility. -/
noncomputable def localClusterPoly (ω : k) (K d : ℕ) (β : Fin d → regularAt ω)
    (i : ClusterIndex K d) : (regularAt ω)[X] :=
  movingClusterComplement (localBase ω) K d i.1.val * (X-C (β i.1))^i.2.val

theorem map_localClusterPoly (ω : k) (K d : ℕ) (hd : 0<d) (hω : ω^d=1)
    (β : Fin d → regularAt ω) (hβ : ∀ r, localEval ω (β r)=ω^r.val)
    (i : ClusterIndex K d) :
    (localClusterPoly ω K d β i).map (localEval ω) =
      QZeta3.clusterBasis (fun r : Fin d => ω^r.val)
        (fun r : Fin d => clusterMultiplicity K d r.val) i := by
  simp only [localClusterPoly, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, hβ]
  have hcomp : (movingClusterComplement (localBase ω) K d i.1.val).map (localEval ω) =
      movingClusterComplement ω K d i.1.val := by
    simp only [movingClusterComplement, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, Polynomial.map_pow, map_pow, localEval_localBase]
  rw [hcomp, movingClusterComplement_reduction ω K d hd hω]
  rfl

noncomputable def localClusterMatrix (ω : k) (K d : ℕ) (β : Fin d → regularAt ω) :
    Matrix (Fin (Fintype.card (ClusterIndex K d))) (Fin (Fintype.card (ClusterIndex K d)))
      (regularAt ω) :=
  Matrix.of fun i j => (localClusterPoly ω K d β ((Fintype.equivFin (ClusterIndex K d)).symm i)).coeff j.val

/-- Every lifted cluster basis has unit determinant in the local ring. -/
theorem localClusterMatrix_det_isUnit {ω : k} {K d : ℕ} (hω : IsPrimitiveRoot ω d)
    (hd : 0<d) (hdK : d≤K) (β : Fin d → regularAt ω)
    (hβ : ∀ r, localEval ω (β r)=ω^r.val) :
    IsUnit (localClusterMatrix ω K d β).det := by
  apply isUnit_of_localEval_ne_zero
  have hmap : (localClusterMatrix ω K d β).map (localEval ω) =
      QZeta3.clusterBasisMatrix (fun r : Fin d => ω^r.val)
        (fun r : Fin d => clusterMultiplicity K d r.val) := by
    ext i j
    change localEval ω ((localClusterPoly ω K d β ((Fintype.equivFin (ClusterIndex K d)).symm i)).coeff j.val)=_
    rw [← Polynomial.coeff_map, map_localClusterPoly ω K d hd hω.pow_eq_one β hβ]
    rfl
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap]
  apply QZeta3.clusterBasisMatrix_det_ne_zero
  · intro r s h
    exact Fin.ext (hω.pow_inj r.isLt s.isLt h)
  · intro r
    exact clusterMultiplicity_pos K d hd hdK r.val r.isLt
end QZeta3.Generic
