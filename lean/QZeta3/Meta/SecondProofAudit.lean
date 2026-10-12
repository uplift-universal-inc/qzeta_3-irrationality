import QZeta3.ElementarySecondProof
import QZeta3.Frozen.Theorem11
import QZeta3Audit.Solution
import Lean

/-!
# Audit of the second proof's project dependencies

This is a build-time dependency check, separate from the kernel axiom audit.
It checks proof bodies as well as statement types. Mathlib cannot depend on
this project, so recursion can stop at names outside its public and private
namespaces. The first proof is a positive control for the traversal.
-/

open Lean Elab Command

private def isProjectName (n : Name) : Bool :=
  n.toString.startsWith "QZeta3." || n.toString.startsWith "_private.QZeta3." ||
    n.toString.startsWith "QZeta3Challenge." || n.toString.startsWith "_private.QZeta3Audit."

private partial def projectDependencies (env : Environment) (n : Name)
    (seen : NameSet := {}) : NameSet := Id.run do
  if seen.contains n then return seen
  let mut seen := seen.insert n
  if !isProjectName n then return seen
  match env.find? n with
  | none => return seen
  | some ci =>
    let mut refs := ci.type.getUsedConstants
    if let some value := ci.value? true then
      refs := refs ++ value.getUsedConstants
    for next in refs do
      if isProjectName next then
        seen := projectDependencies env next seen
    return seen

run_cmd do
  let env := (← getEnv).setExporting false
  let first := projectDependencies env ``QZeta3.theorem11
  unless first.contains ``QZeta3.irrational_xi &&
      first.contains ``QZeta3.content_coeff_proved do
    throwError "Dependency traversal failed its first-proof positive control"
  let wrapper := projectDependencies env ``QZeta3Challenge.irrational_qzeta3
  unless wrapper.contains ``QZeta3.theorem11 do
    throwError "Dependency traversal failed its explicit-series wrapper positive control"
  let second := projectDependencies env ``QZeta3.irrational_qzeta3_elementary
  let required := #[``QZeta3.content_coeff_elementary,
    ``QZeta3.gaussian_residue_identity, ``QZeta3.gaussian_residue_integral,
    ``QZeta3.log_CK_elementary_le, ``QZeta3.irrational_of_poly_approx]
  for name in required do
    unless second.contains name do
      throwError "Second proof is missing the intended dependency {name}"
  let forbidden := #[``QZeta3.theorem11, ``QZeta3.irrational_xi,
    ``QZeta3Challenge.irrational_qzeta3,
    ``QZeta3.PK_coeff_den, ``QZeta3.content_coeff, ``QZeta3.content_coeff_proved,
    ``QZeta3.contentMatrix_coeff_integral, ``QZeta3.mConst_sub_translation_mem,
    ``QZeta3.localTrunc_residue_mem, ``QZeta3.mLin_mem_baseIntegral,
    ``QZeta3.residue_sum_mem_baseIntegral]
  for name in forbidden do
    if second.contains name then
      throwError "Second proof unexpectedly uses the first arithmetic branch: {name}"
  logInfo m!"Second proof dependency audit passed: {second.toArray.size} project declarations; required Gaussian/content/sieve/criterion branch present; {forbidden.size} original-branch declarations absent."

