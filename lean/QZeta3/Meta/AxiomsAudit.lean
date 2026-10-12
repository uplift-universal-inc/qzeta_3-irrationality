import QZeta3.Frozen.Theorem11
import QZeta3.Consistency.Series
import QZeta3Audit.Solution
import QZeta3.ElementarySecondProof

/-!
# Axioms of the stated theorems

Prints the axioms of every frozen statement (`QZeta3.Frozen.*`) and of the proved layer.
Run after the library is built:

    lake env lean QZeta3/Meta/AxiomsAudit.lean

A complete formalisation prints only `[propext, Classical.choice, Quot.sound]` for every line;
`sorryAx` marks a statement whose proof still depends on a `sorry`.
-/

-- Frozen statements of the manuscript
#print axioms QZeta3.theorem11
#print axioms QZeta3Challenge.irrational_qzeta3
#print axioms QZeta3.analytic_bound
#print axioms QZeta3.content_coeff
#print axioms QZeta3.leading_coeff
#print axioms QZeta3.denominators_clear
#print axioms QZeta3.log_CK_sieve_le
#print axioms QZeta3.frequently_ne_zero

-- Fully proved layer (must not mention `sorryAx`)
#print axioms QZeta3.irrational_of_poly_approx
#print axioms QZeta3.tendsto_pow_mul_epsK
#print axioms QZeta3.log_pow_mul_epsK_le
#print axioms QZeta3.summable_term
#print axioms QZeta3.hasSum_xi
#print axioms QZeta3.xi_pos
#print axioms QZeta3.g_inv
#print axioms QZeta3.S_eq_sum_g
#print axioms QZeta3.bK_ge
#print axioms QZeta3.natDegree_Delta_le
#print axioms QZeta3.CK_pos
#print axioms QZeta3.margin_pos
#print axioms QZeta3.F_eval_zero
#print axioms QZeta3.PK_coeff_den
#print axioms QZeta3.abs_aeval_PK_le
#print axioms QZeta3.den_eq_one_of_coprime
#print axioms QZeta3.log_CK_eq
#print axioms QZeta3.sum_cApp_le
#print axioms QZeta3.sum_inv_le_one_add_log
#print axioms QZeta3.cauchyF_eq
#print axioms QZeta3.theta_theta_inv_sub
#print axioms QZeta3.Delta_one
#print axioms QZeta3.eval_Delta_two_two
#print axioms QZeta3.xi_eq_tsum

-- Sufficient finite-sieve growth and the two local denominator ranges.
#print axioms QZeta3.log_CK_rational_le
#print axioms QZeta3.sum_cApp_totient_rational_le
#print axioms QZeta3.rational_cost_margin
#print axioms QZeta3.Generic.low_cyclotomic_bound
#print axioms QZeta3.Generic.high_Delta_scaled_coeff_mem

-- Elementary second proof: Gaussian arithmetic and the source's rational margin.
#print axioms QZeta3.gaussian_residue_identity
#print axioms QZeta3.gaussianBinomial_pascal
#print axioms QZeta3.geometricResidue_low
#print axioms QZeta3.gaussian_residue_integral
#print axioms QZeta3.geometricResidue_reciprocal
#print axioms QZeta3.content_coeff_elementary
#print axioms QZeta3.elementary_cost_margin_eq
#print axioms QZeta3.log_CK_elementary_le
#print axioms QZeta3.tendsto_pow_mul_epsK_elementary
#print axioms QZeta3.PK_coeff_den_elementary
#print axioms QZeta3.irrational_xi_elementary
#print axioms QZeta3.irrational_qzeta3_elementary
