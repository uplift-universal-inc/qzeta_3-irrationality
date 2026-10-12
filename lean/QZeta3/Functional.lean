import QZeta3.Purity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Polynomial Finset Filter Topology

namespace QZeta3

theorem theta_congr_nhds {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] g) :
    theta f =ᶠ[𝓝 x] theta g := by
  exact h.deriv.mono fun y hy => by simp only [theta, hy]

theorem theta_sq_congr_nhds {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] g) :
    theta (theta f) x = theta (theta g) x :=
  (theta_congr_nhds (theta_congr_nhds h)).eq_of_nhds

theorem theta_add {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    theta (f + g) x = theta f x + theta g x := by
  simp only [theta, deriv_add hf hg, mul_add]

theorem theta_const_mul {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    theta (fun y => c * f y) x = c * theta f x := by
  simp only [theta, deriv_const_mul c hf]
  ring

theorem differentiableAt_theta {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (theta f) x := by
  exact differentiableAt_id.mul ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num))

theorem theta_sq_add {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    theta (theta (f + g)) x = theta (theta f) x + theta (theta g) x := by
  have he : theta (f + g) =ᶠ[𝓝 x] theta f + theta g := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact theta_add (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  rw [(theta_congr_nhds he).eq_of_nhds]
  exact theta_add (differentiableAt_theta hf) (differentiableAt_theta hg)

theorem theta_sq_const_mul {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (c : ℝ) :
    theta (theta (fun y => c * f y)) x = c * theta (theta f) x := by
  have he : theta (fun y => c * f y) =ᶠ[𝓝 x] (fun y => c * theta f y) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact theta_const_mul (hy.differentiableAt (by norm_num)) c
  rw [(theta_congr_nhds he).eq_of_nhds]
  exact theta_const_mul (differentiableAt_theta hf) c

theorem theta_sq_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) {x : ℝ}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    theta (theta (fun y => ∑ i ∈ s, f i y)) x = ∑ i ∈ s, theta (theta (f i)) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    have hz : theta (fun _ : ℝ => 0) = (fun _ => 0) := by funext y; simp [theta]
    rw [hz, hz]
  | @insert i s hi ih =>
    have hfi := hf i (mem_insert_self i s)
    have hfs : ∀ j ∈ s, ContDiffAt ℝ 2 (f j) x := fun j hj => hf j (mem_insert_of_mem hj)
    simp only [sum_insert hi]
    change theta (theta (f i + (fun y => ∑ j ∈ s, f j y))) x = _
    rw [theta_sq_add hfi (ContDiffAt.sum hfs), ih hfs]

/-- Finite sums may be passed through the functional when their individual series converge. -/
theorem hasSum_functional_sum {p : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (v : ι → ℝ)
    (hf : ∀ i ∈ s, ∀ m : ℕ, ContDiffAt ℝ 2 (f i) (((p : ℝ)⁻¹)^(m + 1)))
    (hs : ∀ i ∈ s, HasSum (fun m : ℕ => theta (theta (f i))
      (((p : ℝ)⁻¹)^(m + 1))) (v i)) :
    HasSum (fun m : ℕ => theta (theta (fun x => ∑ i ∈ s, f i x))
      (((p : ℝ)⁻¹)^(m + 1))) (∑ i ∈ s, v i) := by
  apply (hasSum_sum hs).congr_fun
  intro m
  exact theta_sq_sum s f (fun i hi => hf i hi m)

theorem hasSum_functional_const_mul {p : ℕ} {f : ℝ → ℝ} {v : ℝ}
    (hf : ∀ m : ℕ, ContDiffAt ℝ 2 f (((p : ℝ)⁻¹)^(m + 1)))
    (hs : HasSum (fun m : ℕ => theta (theta f) (((p : ℝ)⁻¹)^(m + 1))) v) (c : ℝ) :
    HasSum (fun m : ℕ => theta (theta (fun x => c * f x))
      (((p : ℝ)⁻¹)^(m + 1))) (c * v) := by
  apply (hs.mul_left c).congr_fun
  intro m
  exact theta_sq_const_mul (hf m) c

theorem hasSum_functional_add {p : ℕ} {f g : ℝ → ℝ} {v w : ℝ}
    (hf : ∀ m : ℕ, ContDiffAt ℝ 2 f (((p : ℝ)⁻¹)^(m + 1)))
    (hg : ∀ m : ℕ, ContDiffAt ℝ 2 g (((p : ℝ)⁻¹)^(m + 1)))
    (hs : HasSum (fun m : ℕ => theta (theta f) (((p : ℝ)⁻¹)^(m + 1))) v)
    (ht : HasSum (fun m : ℕ => theta (theta g) (((p : ℝ)⁻¹)^(m + 1))) w) :
    HasSum (fun m : ℕ => theta (theta (f + g)) (((p : ℝ)⁻¹)^(m + 1))) (v + w) := by
  apply (hs.add ht).congr_fun
  intro m
  exact theta_sq_add (hf m) (hg m)

theorem hasSum_functional_congr {p : ℕ} {f g : ℝ → ℝ} {v : ℝ}
    (he : ∀ m : ℕ, f =ᶠ[𝓝 (((p : ℝ)⁻¹)^(m + 1))] g)
    (hs : HasSum (fun m : ℕ => theta (theta g) (((p : ℝ)⁻¹)^(m + 1))) v) :
    HasSum (fun m : ℕ => theta (theta f) (((p : ℝ)⁻¹)^(m + 1))) v := by
  apply hs.congr_fun
  intro m
  exact theta_sq_congr_nhds (he m)

/-- Evaluation of a rational polynomial is smooth, by its finite coefficient expansion. -/
theorem contDiffAt_ratPolynomial (P : ℚ[X]) (x : ℝ) :
    ContDiffAt ℝ 2 (fun y => P.eval₂ (Rat.castHom ℝ) y) x := by
  simp only [eval₂_eq_sum, Polynomial.sum_def]
  apply ContDiffAt.sum
  intro j hj
  exact contDiffAt_const.mul (contDiffAt_id.pow j)

/-- The functional applied to any rational polynomial has its prescribed rational moment sum. -/
theorem hasSum_polynomial {p : ℕ} (hp : 2 ≤ p) (P : ℚ[X]) :
    HasSum (fun m : ℕ => theta (theta (fun x => P.eval₂ (Rat.castHom ℝ) x))
      (((p : ℝ)⁻¹)^(m + 1))) (Lpoly p P : ℝ) := by
  simp only [eval₂_eq_sum, Polynomial.sum_def]
  have hs := hasSum_functional_sum P.support
    (fun j x => (P.coeff j : ℝ) * x^j) (fun j => (P.coeff j : ℝ) * (mu p j : ℝ))
    (fun j _ m => contDiffAt_const.mul (contDiffAt_id.pow j))
    (fun j _ => hasSum_functional_const_mul (fun _ => contDiffAt_id.pow j)
      (hasSum_monomial hp j) (P.coeff j : ℝ))
  simpa only [Lpoly, Rat.cast_sum, Rat.cast_mul, Rat.coe_castHom] using hs

theorem contDiffAt_simplePole {p a : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    ContDiffAt ℝ 2 (fun x => (1 - ((p : ℝ)⁻¹)^a * x)⁻¹)
      (((p : ℝ)⁻¹)^(m + 1)) := by
  have hn : 1 - ((p : ℝ)⁻¹)^a * ((p : ℝ)⁻¹)^(m + 1) ≠ 0 := by
    rw [← pow_add]
    exact ne_of_gt (sub_pos.mpr (inv_base_pow_lt_one hp (by omega)))
  exact (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)).inv hn

theorem hasSum_simplePole {p : ℕ} (hp : 2 ≤ p) (a : ℕ) (ha : 1 ≤ a) :
    HasSum (fun m : ℕ => theta (theta (fun x => (1 - ((p : ℝ)⁻¹)^a * x)⁻¹))
      (((p : ℝ)⁻¹)^(m + 1))) (xi p - (S p a : ℝ)) := by
  have ht : Summable (fun m : ℕ => poleKernel p (m + a + 1)) :=
    (summable_nat_add_iff a).mpr (hasSum_poleKernel hp).summable
  have he : (fun m : ℕ => theta (theta (fun x => (1 - ((p : ℝ)⁻¹)^a * x)⁻¹))
      (((p : ℝ)⁻¹)^(m + 1))) = (fun m : ℕ => poleKernel p (m + a + 1)) := by
    funext m
    have hn : 1 - ((p : ℝ)⁻¹)^a * ((p : ℝ)⁻¹)^(m + 1) ≠ 0 := by
      rw [← pow_add]
      exact ne_of_gt (sub_pos.mpr (inv_base_pow_lt_one hp (by omega)))
    rw [theta_sq_inv_affine hn]
    have he : a + (m + 1) = m + a + 1 := by omega
    simp only [poleKernel, ← pow_add, he]
  have hs : Summable (fun m : ℕ => theta (theta
      (fun x => (1 - ((p : ℝ)⁻¹)^a * x)⁻¹)) (((p : ℝ)⁻¹)^(m + 1))) := he ▸ ht
  have heval := purity hp a ha
  exact heval ▸ hs.hasSum

end QZeta3
