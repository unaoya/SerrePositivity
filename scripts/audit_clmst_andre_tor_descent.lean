import SerrePositivity.CLMST.AndreTorDescent
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.isCompletelyFlat_of_linearEquiv
assert_no_sorry SerrePositivity.isCompletelyFaithfullyFlat_of_linearEquiv
#print axioms SerrePositivity.isCompletelyFlat_of_linearEquiv
#print axioms SerrePositivity.isCompletelyFaithfullyFlat_of_linearEquiv
#print axioms SerrePositivity.CLMST.exists_andre_extension_detects_powerTorsion_Tor

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits SerrePositivity SerrePositivity.CLMST
attribute [local instance] HasDerivedCategory.standard

-- A single actual extension works for all torsion modules and positive degrees.
theorem audit_andre_extension_actual_base_coefficient_Tor
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      IsIntegralPerfectoid E p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) E ∧
      IsAbsolutelyIntegrallyClosed E ∧
      ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
        ∀ i : ℕ, 0 < i → IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat E) (-(i : ℤ))).obj
            ((boundedAboveDerivedBaseChange (algebraMap R E)).obj
              (boundedAboveDerivedTensor.obj
                (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R),
                  boundedAboveDerivedSingleFunctor.obj N))).obj) := by
  obtain ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, hdet⟩ :=
    exists_andre_extension_detects_powerTorsion_Tor R p hR
  letI := hEring
  letI := hEalg
  refine ⟨E, hEring, hEalg, hE, hflat, haic, ?_⟩
  intro N k hN i hi
  have hz : IsZero (((Tor (ModuleCat R) i).obj (ModuleCat.of R R)).obj N) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (torModule_subsingleton_of_flat (R := R) R N j)
  have hs := (hdet R N k hN i 1).mp (hz.eq_of_src _ _)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  let X := (boundedAboveDerivedBaseChange (algebraMap R E)).obj
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R),
        boundedAboveDerivedSingleFunctor.obj N))
  have hzero : ∀ x : (DerivedCategory.homologyFunctor (ModuleCat E) (-(i : ℤ))).obj X.obj,
      x = 0 := by
    intro x
    simpa only [map_one, one_smul] using hs x
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

#print axioms audit_andre_extension_actual_base_coefficient_Tor

theorem audit_andre_extension_completed_base_coefficient_Tor
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      IsIntegralPerfectoid E p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) E ∧
      IsAbsolutelyIntegrallyClosed E ∧
      ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
        ∀ i : ℕ, 0 < i →
          let X := (DerivedCompletion.boundedAboveDerivedCompletionFunctor E (p : E)).obj
            ((boundedAboveDerivedBaseChange (algebraMap R E)).obj
              (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R)))
          ∀ x : (((Tor (ModuleCat E) i).obj
            ((DerivedCategory.homologyFunctor (ModuleCat E) 0).obj X.obj)).obj
              ((ModuleCat.extendScalars (algebraMap R E)).obj N)), x = 0 := by
  obtain ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, hdet⟩ :=
    exists_andre_extension_detects_completedBaseChangeTor R p hR
  letI := hEring
  letI := hEalg
  refine ⟨E, hEring, hEalg, hE, hflat, haic, ?_⟩
  intro N k hN i hi
  have hz : IsZero (((Tor (ModuleCat R) i).obj (ModuleCat.of R R)).obj N) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (torModule_subsingleton_of_flat (R := R) R N j)
  have hs := (hdet R hR N k hN i 1).mp (hz.eq_of_src _ _)
  simpa only [map_one, one_smul] using hs

#print axioms SerrePositivity.CLMST.exists_andre_extension_detects_completedBaseChangeTor
#print axioms audit_andre_extension_completed_base_coefficient_Tor

meta section
open Lean Elab Command
private partial def checkAndreTorDependencies (todo : List Name) (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← checkAndreTorDependencies rest seen
    let seen := seen.insert n
    let some info := (← getEnv).find? n | return ← checkAndreTorDependencies rest seen
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx &&
        n != ``SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed then
      throwError "Unapproved sorry in André Tor descent: {n}"
    checkAndreTorDependencies (deps.toList ++ rest) seen

elab "assert_andre_tor_dependencies" : command => do
  let roots := [``SerrePositivity.CLMST.exists_andre_extension_detects_powerTorsion_Tor,
    ``audit_andre_extension_actual_base_coefficient_Tor,
    ``SerrePositivity.CLMST.exists_andre_extension_detects_completedBaseChangeTor,
    ``audit_andre_extension_completed_base_coefficient_Tor]
  let seen ← liftCoreM <| checkAndreTorDependencies roots {}
  unless seen.contains
      ``SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed do
    throwError "Expected existing BS Theorem 7.14 dependency is missing"
  logInfo "André Tor descent: only the existing BS Theorem 7.14 sorry is permitted."
end

assert_andre_tor_dependencies
