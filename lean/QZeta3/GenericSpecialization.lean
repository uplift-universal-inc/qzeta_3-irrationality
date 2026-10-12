import QZeta3.GenericMoments

open Polynomial Finset

namespace QZeta3.Generic.Specialization

variable {𝕜 𝕝 : Type*} [Field 𝕜] [Field 𝕝] {R : Subring 𝕜}

/-- Graph of a specialization defined on a subring of the source field. -/
def Maps (φ : R →+* 𝕝) (a : 𝕜) (b : 𝕝) : Prop :=
  ∃ r : R, (r : 𝕜) = a ∧ φ r = b

variable {φ : R →+* 𝕝}

namespace Maps

theorem of_mem {a : 𝕜} (ha : a ∈ R) : Maps φ a (φ ⟨a, ha⟩) := ⟨⟨a, ha⟩, rfl, rfl⟩
theorem zero : Maps φ 0 0 := ⟨0, rfl, map_zero φ⟩
theorem one : Maps φ 1 1 := ⟨1, rfl, map_one φ⟩
theorem natCast (n : ℕ) : Maps φ (n : 𝕜) (n : 𝕝) := ⟨n, by simp, map_natCast φ n⟩
theorem neg {a : 𝕜} {b : 𝕝} (h : Maps φ a b) : Maps φ (-a) (-b) := by
  obtain ⟨r, rfl, rfl⟩ := h
  exact ⟨-r, rfl, map_neg φ r⟩
theorem add {a c : 𝕜} {b d : 𝕝} (h : Maps φ a b) (h' : Maps φ c d) :
    Maps φ (a+c) (b+d) := by
  obtain ⟨r, rfl, rfl⟩ := h
  obtain ⟨s, rfl, rfl⟩ := h'
  exact ⟨r+s, rfl, map_add φ r s⟩
theorem sub {a c : 𝕜} {b d : 𝕝} (h : Maps φ a b) (h' : Maps φ c d) :
    Maps φ (a-c) (b-d) := by
  simpa only [sub_eq_add_neg] using h.add h'.neg
 theorem mul {a c : 𝕜} {b d : 𝕝} (h : Maps φ a b) (h' : Maps φ c d) :
    Maps φ (a*c) (b*d) := by
  obtain ⟨r, rfl, rfl⟩ := h
  obtain ⟨s, rfl, rfl⟩ := h'
  exact ⟨r*s, rfl, map_mul φ r s⟩
theorem pow {a : 𝕜} {b : 𝕝} (h : Maps φ a b) (n : ℕ) : Maps φ (a^n) (b^n) := by
  obtain ⟨r, rfl, rfl⟩ := h
  exact ⟨r^n, by simp, map_pow φ r n⟩
theorem sum {ι : Type*} (s : Finset ι) {f : ι → 𝕜} {g : ι → 𝕝}
    (h : ∀ i ∈ s, Maps φ (f i) (g i)) : Maps φ (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (φ := φ))
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))
theorem prod {ι : Type*} (s : Finset ι) {f : ι → 𝕜} {g : ι → 𝕝}
    (h : ∀ i ∈ s, Maps φ (f i) (g i)) : Maps φ (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one (φ := φ))
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))
theorem inv {a : 𝕜} {b : 𝕝} (h : Maps φ a b) (hi : a⁻¹ ∈ R) :
    Maps φ a⁻¹ b⁻¹ := by
  by_cases ha : a = 0
  · subst a
    obtain ⟨r, hr, hφ⟩ := h
    have hr0 : r=0 := Subtype.ext hr
    simp only [hr0, map_zero] at hφ
    subst b
    simpa using (zero (φ := φ))
  obtain ⟨r, hr, hφ⟩ := h
  let s : R := ⟨a⁻¹, hi⟩
  have he : r*s = 1 := by apply Subtype.ext; simpa [s, hr] using mul_inv_cancel₀ ha
  have heφ : φ r*φ s=1 := by rw [← map_mul, he, map_one]
  refine ⟨s, rfl, ?_⟩
  rw [← hφ]
  exact eq_inv_of_mul_eq_one_right heφ

theorem value {a : 𝕜} {b : 𝕝} (h : Maps φ a b) (ha : a ∈ R) : φ ⟨a,ha⟩=b := by
  obtain ⟨r, hr, hφ⟩ := h
  have : (⟨a,ha⟩ : R)=r := Subtype.ext hr.symm
  simpa [this] using hφ

end Maps

/-- Coefficientwise specialization of a polynomial, witnessed by a polynomial
in the common subring. -/
def MapsPolynomial (φ : R →+* 𝕝) (f : 𝕜[X]) (g : 𝕝[X]) : Prop :=
  ∃ F : R[X], F.map R.subtype=f ∧ F.map φ=g

namespace MapsPolynomial

theorem add {f f' : 𝕜[X]} {g g' : 𝕝[X]} (h : MapsPolynomial φ f g)
    (h' : MapsPolynomial φ f' g') : MapsPolynomial φ (f+f') (g+g') := by
  obtain ⟨F, rfl, rfl⟩ := h
  obtain ⟨G, rfl, rfl⟩ := h'
  exact ⟨F+G, by simp, by simp⟩
theorem mul {f f' : 𝕜[X]} {g g' : 𝕝[X]} (h : MapsPolynomial φ f g)
    (h' : MapsPolynomial φ f' g') : MapsPolynomial φ (f*f') (g*g') := by
  obtain ⟨F, rfl, rfl⟩ := h
  obtain ⟨G, rfl, rfl⟩ := h'
  exact ⟨F*G, by simp, by simp⟩

theorem X : MapsPolynomial φ (Polynomial.X : 𝕜[X]) (Polynomial.X : 𝕝[X]) :=
  ⟨Polynomial.X, by simp, by simp⟩
theorem C {a : 𝕜} {b : 𝕝} (h : Maps φ a b) : MapsPolynomial φ (Polynomial.C a) (Polynomial.C b) := by
  obtain ⟨r, rfl, rfl⟩ := h
  exact ⟨Polynomial.C r, by simp, by simp⟩
theorem sub {f f' : 𝕜[X]} {g g' : 𝕝[X]} (h : MapsPolynomial φ f g)
    (h' : MapsPolynomial φ f' g') : MapsPolynomial φ (f-f') (g-g') := by
  obtain ⟨F, rfl, rfl⟩ := h
  obtain ⟨G, rfl, rfl⟩ := h'
  exact ⟨F-G, by simp, by simp⟩
theorem pow {f : 𝕜[X]} {g : 𝕝[X]} (h : MapsPolynomial φ f g) (n : ℕ) :
    MapsPolynomial φ (f^n) (g^n) := by
  obtain ⟨F, rfl, rfl⟩ := h
  exact ⟨F^n, by simp, by simp⟩
theorem prod {ι : Type*} (s : Finset ι) {f : ι → 𝕜[X]} {g : ι → 𝕝[X]}
    (h : ∀ i ∈ s, MapsPolynomial φ (f i) (g i)) :
    MapsPolynomial φ (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  choose F hF using fun i : s => h i i.property
  refine ⟨∏ i : s, F i, ?_, ?_⟩
  · simpa only [Polynomial.map_prod, hF, Finset.prod_coe_sort]
  · simpa only [Polynomial.map_prod, hF, Finset.prod_coe_sort]
theorem coeff {f : 𝕜[X]} {g : 𝕝[X]} (h : MapsPolynomial φ f g) (i : ℕ) :
    Maps φ (f.coeff i) (g.coeff i) := by
  obtain ⟨F, rfl, rfl⟩ := h
  exact ⟨F.coeff i, by simp, by simp⟩
theorem derivative {f : 𝕜[X]} {g : 𝕝[X]} (h : MapsPolynomial φ f g) :
    MapsPolynomial φ f.derivative g.derivative := by
  obtain ⟨F, rfl, rfl⟩ := h
  exact ⟨F.derivative, by simp, by simp⟩
theorem eval {f : 𝕜[X]} {g : 𝕝[X]} {a : 𝕜} {b : 𝕝}
    (h : MapsPolynomial φ f g) (hab : Maps φ a b) : Maps φ (f.eval a) (g.eval b) := by
  obtain ⟨F, rfl, rfl⟩ := h
  obtain ⟨r, rfl, rfl⟩ := hab
  exact ⟨F.eval r, (Polynomial.eval_map_apply R.subtype r).symm,
    (Polynomial.eval_map_apply φ r).symm⟩

theorem divByMonic {f d : 𝕜[X]} {g e : 𝕝[X]} (h : MapsPolynomial φ f g)
    (hd : MapsPolynomial φ d e) (hm : d.Monic) :
    MapsPolynomial φ (f /ₘ d) (g /ₘ e) := by
  obtain ⟨F, rfl, rfl⟩ := h
  obtain ⟨D, rfl, rfl⟩ := hd
  have hD : D.Monic := Polynomial.monic_of_injective Subtype.val_injective hm
  exact ⟨F /ₘ D, Polynomial.map_divByMonic R.subtype hD,
    Polynomial.map_divByMonic φ hD⟩

theorem det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι 𝕜[X]} {N : Matrix ι ι 𝕝[X]}
    (h : ∀ i j, MapsPolynomial φ (M i j) (N i j)) :
    MapsPolynomial φ M.det N.det := by
  classical
  choose F hF hG using h
  refine ⟨Matrix.det (Matrix.of F), ?_, ?_⟩
  · change (Polynomial.mapRingHom R.subtype) (Matrix.det (Matrix.of F)) = M.det
    rw [RingHom.map_det]
    congr 1
    apply Matrix.ext
    intro i j
    exact hF i j
  · change (Polynomial.mapRingHom φ) (Matrix.det (Matrix.of F)) = N.det
    rw [RingHom.map_det]
    congr 1
    apply Matrix.ext
    intro i j
    exact hG i j

end MapsPolynomial

variable {z : 𝕜} {w : 𝕝} {K : ℕ}

theorem maps_F (hz : Maps φ z w) (K : ℕ) : MapsPolynomial φ (F z K) (F w K) := by
  apply MapsPolynomial.prod
  intro a ha
  exact MapsPolynomial.X.sub (MapsPolynomial.C (hz.pow a))

theorem maps_res (h : LocalizationData R z K) (hz : Maps φ z w) (k a : ℕ)
    (ha : a ∈ Icc 1 K) : Maps φ (res z K k a) (res w K k a) := by
  unfold res
  simp only [div_eq_mul_inv]
  exact (hz.pow _).mul (((maps_F hz K).derivative.eval (hz.pow a)).inv
    (h.inverse_derivative_mem a ha))

theorem maps_S (h : LocalizationData R z K) (hz : Maps φ z w) (a : ℕ) (ha : a ≤ K) :
    Maps φ (S z a) (S w a) := by
  apply Maps.sum
  intro b hb
  simp only [div_eq_mul_inv, ← inv_pow]
  exact ((hz.pow b).mul ((hz.pow b).add Maps.one)).mul
    ((((hz.pow b).sub Maps.one).inv
      (h.inv_geom_mem b (mem_Icc.mpr ⟨(mem_Icc.mp hb).1, (mem_Icc.mp hb).2.trans ha⟩))).pow 3)

theorem maps_mu (h : LocalizationData R z K) (hz : Maps φ z w) (j : ℕ) (hj : j ≤ K) :
    Maps φ (mu z j) (mu w j) := by
  unfold mu
  split_ifs with hzero
  · exact Maps.zero
  · simp only [div_eq_mul_inv]
    exact ((Maps.natCast j).pow 2).mul (((hz.pow j).sub Maps.one).inv
      (h.inv_geom_mem j (mem_Icc.mpr ⟨by omega, hj⟩)))

theorem maps_mLin (h : LocalizationData R z K) (hz : Maps φ z w) (k : ℕ) :
    Maps φ (mLin z K k) (mLin w K k) := by
  apply Maps.neg
  apply Maps.sum
  intro a ha
  simp only [div_eq_mul_inv, ← inv_pow]
  exact (maps_res h hz k a ha).mul ((hz.inv h.inv_base_mem).pow a)

theorem Lpoly_eq_sum_range (z : 𝕜) (f : 𝕜[X]) (n : ℕ) (hn : f.natDegree < n) :
    Lpoly z f = ∑ j ∈ range n, f.coeff j * mu z j := by
  change f.sum (fun j c => c * mu z j) = _
  exact f.sum_over_range' (f := fun j c => c * mu z j) (fun j => zero_mul (mu z j)) n hn

theorem maps_quotient_moment (h : LocalizationData R z K) (hz : Maps φ z w)
    (k : ℕ) (hk : k ≤ 2*K) :
    Maps φ (Lpoly z (X^k /ₘ F z K)) (Lpoly w (X^k /ₘ F w K)) := by
  have hd (v : 𝕜) : (X^k /ₘ F v K).natDegree < K+1 := by
    rw [Polynomial.natDegree_divByMonic _ (F_monic v K), Polynomial.natDegree_X_pow, F_natDegree]
    omega
  have hw : (X^k /ₘ F w K).natDegree < K+1 := by
    rw [Polynomial.natDegree_divByMonic _ (F_monic w K), Polynomial.natDegree_X_pow, F_natDegree]
    omega
  rw [Lpoly_eq_sum_range z _ (K+1) (hd z), Lpoly_eq_sum_range w _ (K+1) hw]
  apply Maps.sum
  intro j hj
  exact (((MapsPolynomial.X.pow k).divByMonic (maps_F hz K) (F_monic z K)).coeff j).mul
    (maps_mu h hz j (by have := mem_range.mp hj; omega))

theorem maps_mConst (h : LocalizationData R z K) (hz : Maps φ z w)
    (k : ℕ) (hk : k ≤ 2*K) : Maps φ (mConst z K k) (mConst w K k) := by
  apply Maps.add (maps_quotient_moment h hz k hk)
  apply Maps.sum
  intro a ha
  simp only [div_eq_mul_inv, ← inv_pow]
  exact ((maps_res h hz k a ha).mul (maps_S h hz a (mem_Icc.mp ha).2)).mul
    ((hz.inv h.inv_base_mem).pow a)

theorem maps_nrm (hz : Maps φ z w) (K : ℕ) : Maps φ (nrm z K) (nrm w K) :=
  ((Maps.one.neg).pow K).mul (hz.pow (AK K))

theorem maps_Delta (h : LocalizationData R z K) (hz : Maps φ z w) :
    MapsPolynomial φ (Delta z K) (Delta w K) := by
  apply MapsPolynomial.det
  intro i j
  exact (MapsPolynomial.X.mul (MapsPolynomial.C
    ((maps_nrm hz K).mul (maps_mLin h hz (i.val+j.val))))).add
    (MapsPolynomial.C ((maps_nrm hz K).mul (maps_mConst h hz (i.val+j.val)
      (by have := i.isLt; have := j.isLt; omega))))

/-- The original determinant commutes with every specialization defined on its
localization ring. -/
theorem specialize_Delta_coeff (h : LocalizationData R z K) (φ : R →+* 𝕝) (i : ℕ) :
    φ ⟨(Delta z K).coeff i, h.Delta_coeff_mem i⟩ =
      (Delta (φ ⟨z, h.base_mem⟩) K).coeff i :=
  ((maps_Delta h (Maps.of_mem h.base_mem)).coeff i).value (h.Delta_coeff_mem i)

theorem map_Delta (f : 𝕜 →+* 𝕝) (z : 𝕜) (K : ℕ) :
    (Delta z K).map f = Delta (f z) K := by
  let h : LocalizationData (⊤ : Subring 𝕜) z K := ⟨by trivial, by trivial, by intros; trivial⟩
  ext i
  simpa using specialize_Delta_coeff h (f.comp (⊤ : Subring 𝕜).subtype) i

end QZeta3.Generic.Specialization
