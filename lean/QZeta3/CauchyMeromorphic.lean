import QZeta3.CauchyPole
import QZeta3.CauchyExterior
import Mathlib.Analysis.Meromorphic.Order

open Filter Topology Polynomial

namespace QZeta3

theorem meromorphicAt_cauchyKernel (p n : ℕ) (z : ℝ) :
    MeromorphicAt (cauchyKernel p n) z := by
  unfold cauchyKernel
  exact ((MeromorphicAt.const _ z).mul
    ((MeromorphicAt.id z).add (MeromorphicAt.const _ z))).div
    (((MeromorphicAt.id z).sub (MeromorphicAt.const _ z)).pow 3)

/-- At every positive point, a finite rational head and a scaled analytic
tail give a meromorphic expression for the Cauchy transform. -/
theorem meromorphicOn_cauchySeries_pos {p : ℕ} (hp : 2 ≤ p) :
    MeromorphicOn (cauchySeries p) (Set.Ioi 0) := by
  intro z hz
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hz (inv_base_lt_one hp)
  let t := ((p : ℝ)⁻¹)^N
  have ht : 0 < t := pow_pos (inv_base_pos hp) _
  have hzt : 1 < z/t := (lt_div_iff₀ ht).mpr (by simpa [t] using hN)
  have hhead : MeromorphicAt
      (fun y : ℝ => ∑ n ∈ Finset.range N, cauchyKernel p n y) z :=
    MeromorphicAt.fun_sum (fun n _ => meromorphicAt_cauchyKernel p n z)
  have hscale : AnalyticAt ℝ (fun y : ℝ => y/t) z := analyticAt_id.div_const
  have htail : AnalyticAt ℝ (fun y : ℝ => t⁻¹*cauchySeries p (y/t)) z :=
    analyticAt_const.mul ((analyticAt_cauchySeries_of_gt_one hp hzt).comp
      (f := fun y : ℝ => y/t) hscale)
  apply (hhead.add htail.meromorphicAt).congr
  have hn : ∀ᶠ y : ℝ in 𝓝 z, t < y := eventually_gt_nhds hN
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with y hy
  have hyt : (p : ℝ)⁻¹ < y/t := lt_trans (inv_base_lt_one hp)
    ((lt_div_iff₀ ht).mpr (by simpa using hy))
  exact (cauchySeries_split hp N y (summable_cauchyKernel_of_gt_q hp hyt)).symm

/-- A meromorphic germ which vanishes at positive infinity vanishes near
every positive real point. -/
theorem meromorphicOn_Ioi_eventually_zero_of_atTop {f : ℝ → ℝ}
    (hf : MeromorphicOn f (Set.Ioi 0))
    (hzero : ∀ᶠ x : ℝ in atTop, f x = 0) {x : ℝ} (hx : 0 < x) :
    ∀ᶠ y : ℝ in 𝓝[≠] x, f y = 0 := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp hzero
  let a := max A 0 + 1
  have ha : 0 < a := by dsimp [a]; linarith [le_max_right A 0]
  have hAa : A < a := by dsimp [a]; linarith [le_max_left A 0]
  have hlocal : ∀ᶠ y : ℝ in 𝓝[≠] a, f y = 0 := by
    have hn : ∀ᶠ y : ℝ in 𝓝 a, A < y :=
      eventually_gt_nhds hAa
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with y hy
    exact hA y (le_of_lt hy)
  apply meromorphicOrderAt_eq_top_iff.mp
  exact hf.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_Ioi ha hx
    (meromorphicOrderAt_eq_top_iff.mpr hlocal)

theorem analyticAt_polynomial_eval (P : ℝ[X]) (x : ℝ) :
    AnalyticAt ℝ (fun y : ℝ => P.eval y) x := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      convert hP.add hQ using 1
      ext y
      simp
  | monomial n c =>
      convert (show AnalyticAt ℝ (fun _ : ℝ => c) x from analyticAt_const).mul
        (analyticAt_id.pow n) using 1
      ext y
      simp

/-- Distinct geometric nodes cannot all be roots of a nonzero polynomial. -/
theorem polynomial_eq_zero_of_geometric_roots {p : ℕ} (hp : 2 ≤ p) (Q : ℝ[X])
    (hQ : ∀ n : ℕ, Q.eval (((p : ℝ)⁻¹)^(n+1)) = 0) : Q = 0 := by
  apply Q.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (f := fun n : Fin (Q.natDegree + 1) => ((p : ℝ)⁻¹)^(n.val+1))
  · intro a b hab
    have hab' := (pow_right_strictAnti₀ (inv_base_pos hp) (inv_base_lt_one hp)).injective hab
    apply Fin.ext
    omega
  · intro n
    exact hQ n.val
  · simp

/-- A nonzero cubic principal part forces every rational denominator to vanish
at its pole whenever the rational identity holds in the punctured germ. -/
theorem polynomial_root_of_cubic_pole {f : ℝ → ℝ} {a c : ℝ} (hc : c ≠ 0)
    (hpole : Tendsto (fun z : ℝ => (z-a)^3*f z) (𝓝[≠] a) (𝓝 c))
    (P Q : ℝ[X]) (heq : ∀ᶠ z : ℝ in 𝓝[≠] a, f z*Q.eval z-P.eval z=0) :
    Q.eval a = 0 := by
  have hQ : Tendsto (fun z : ℝ => Q.eval z) (𝓝[≠] a) (𝓝 (Q.eval a)) :=
    (analyticAt_polynomial_eval Q a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hP : Tendsto (fun z : ℝ => P.eval z) (𝓝[≠] a) (𝓝 (P.eval a)) :=
    (analyticAt_polynomial_eval P a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun z : ℝ => (z-a)^3) (𝓝[≠] a) (𝓝 0) := by
    convert ((tendsto_id.sub_const a).pow 3).mono_left nhdsWithin_le_nhds using 1 <;> simp
  have hlim : Tendsto (fun z : ℝ => (z-a)^3*(f z*Q.eval z-P.eval z))
      (𝓝[≠] a) (𝓝 (c*Q.eval a)) := by
    convert (hpole.mul hQ).sub (hz.mul hP) using 1
    · ext z
      ring
    · simp
  have hlim0 : Tendsto (fun z : ℝ => (z-a)^3*(f z*Q.eval z-P.eval z))
      (𝓝[≠] a) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [heq] with z hz
    simp [hz]
  exact (mul_eq_zero.mp (tendsto_nhds_unique hlim hlim0)).resolve_left hc

end QZeta3
