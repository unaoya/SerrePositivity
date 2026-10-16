import SerrePositivity.CLMST.RPerfdCohomologyInputs
import Mathlib.Util.AssertNoSorry

noncomputable section
universe u
open SerrePositivity SerrePositivity.CLMST SerrePositivity.Section2 IsLocalRing

assert_no_sorry parameter_power_isKoszulResolution
#print axioms parameter_power_isKoszulResolution
#print axioms toRPerfd_algebraMap_A
#print axioms rPerfd_p_coordinate
#print axioms rPerfd_tor_eq_zero_of_finite
#print axioms rPerfd_cohomology_vanishing_of_tor_idempotent

-- The original selected RPerfd has a known existence dependency. Reject all
-- other sorry declarations, including the cohomology and idempotence inputs.
meta section
open Lean Elab Command
private partial def checkRPerfdDependencies (todo : List Name) (visited : NameSet) :
    CoreM NameSet := do
  match todo with
  | [] => return visited
  | n :: todo =>
    if visited.contains n then return ← checkRPerfdDependencies todo visited
    if [ `SerrePositivity.CLMST.Inputs.corollary_4_0_4,
        `SerrePositivity.CLMST.Inputs.proposition_2_4_7,
        `SerrePositivity.CLMST.Inputs.perfectoidIdealMod_idempotent].contains n then
      throwError "Forbidden cohomology input: {n}"
    let visited := visited.insert n
    let some info := (← getEnv).find? n
      | return ← checkRPerfdDependencies todo visited
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx &&
        n != ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral then
      throwError "Unapproved sorry in {n}"
    checkRPerfdDependencies (deps.toList ++ todo) visited

elab "assert_rperfd_cohomology_dependencies" : command => do
  let roots := [``toRPerfd_algebraMap_A, ``rPerfd_p_coordinate,
    ``rPerfd_tor_eq_zero_of_finite, ``rPerfd_cohomology_vanishing_of_tor_idempotent]
  let _ ← liftCoreM <| checkRPerfdDependencies roots {}
  logInfo "Only the existing integral-perfectoidization existence sorry is permitted."
end

assert_rperfd_cohomology_dependencies

variable (A : Type u) [CommRing A] [IsRegularLocalRing A]
    {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)

-- The zero-th power in the actual local-cohomology diagram is included.
example : IsKoszulResolution (fun j => t j ^ (0 : ℕ)) :=
  parameter_power_isKoszulResolution A t ht hdim 0

-- No positivity hypothesis on the number of parameters was added.
example (t₀ : Fin 0 → A) (ht₀ : Ideal.span (Set.range t₀) = maximalIdeal A)
    (hdim₀ : ringKrullDim A = 0) (k : ℕ) :
    IsKoszulResolution (fun j => t₀ j ^ k) :=
  parameter_power_isKoszulResolution A t₀ ht₀ hdim₀ k

variable (D : Type u) [CommRing D] [Algebra A D] [Module.Finite A D]
    (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

-- All finite stages, including zero, retain their original D-algebra action.
example (n : ℕ) (x : A) :
    toRPerfd A D t p hperf n
      (algebraMap D (StageAlgebra A D t p n) (algebraMap A D x)) =
        algebraMap A (RPerfd A D t p hperf) x :=
  toRPerfd_algebraMap_A A t D p hperf n x
