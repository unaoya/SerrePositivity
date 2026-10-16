import SerrePositivity.CLMST.AndrePerfectoidizationTorDescent
import Mathlib.Util.AssertNoSorry

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits SerrePositivity SerrePositivity.CLMST
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

-- The same actual extension works for every selected base-changed coefficient model.
theorem audit_andre_selected_base_coefficient_positive_Tor
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      IsIntegralPerfectoid E p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) E ∧
      IsAbsolutelyIntegrallyClosed E ∧
      ∀ (D : Type u) [CommRing D] [Algebra E D] (g : E ⊗[R] R →ₐ[E] D),
        IsPerfectoidization p g.toRingHom →
        ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
        ∀ i : ℕ, 0 < i →
          ∀ x : (((Tor (ModuleCat E) i).obj (ModuleCat.of E D)).obj
            ((ModuleCat.extendScalars (algebraMap R E)).obj N)), x = 0 := by
  obtain ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, hdet⟩ :=
    exists_andre_extension_detects_baseChangedPerfectoidizationTor R p hR
  letI := hEring
  letI := hEalg
  have hid : IsPerfectoidization p (AlgHom.id R R).toRingHom := by
    refine ⟨hR, ?_⟩
    intro B _ _hB f
    refine ⟨f, ?_, ?_⟩
    · ext x
      rfl
    · intro l hl
      ext x
      exact RingHom.congr_fun hl x
  refine ⟨E, hEring, hEalg, hE, hflat, haic, ?_⟩
  intro D _ _ g hg N k hN i hi
  have hz : IsZero (((Tor (ModuleCat R) i).obj (ModuleCat.of R R)).obj N) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (torModule_subsingleton_of_flat (R := R) R N j)
  have hs := (hdet R R (AlgHom.id R R) hid D g hg N k hN i 1).mp (hz.eq_of_src _ _)
  simpa only [map_one, one_smul] using hs

#print axioms SerrePositivity.CLMST.exists_andre_extension_detects_baseChangedPerfectoidizationTor
#print axioms audit_andre_selected_base_coefficient_positive_Tor

meta section
open Lean Elab Command
private partial def checkSelectedAndreDependencies (todo : List Name) (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← checkSelectedAndreDependencies rest seen
    let seen := seen.insert n
    let some info := (← getEnv).find? n | return ← checkSelectedAndreDependencies rest seen
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx &&
        n != ``SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed then
      throwError "Unapproved sorry in selected André Tor comparison: {n}"
    checkSelectedAndreDependencies (deps.toList ++ rest) seen

elab "assert_selected_andre_dependencies" : command => do
  let roots := [``SerrePositivity.CLMST.exists_andre_extension_detects_baseChangedPerfectoidizationTor,
    ``audit_andre_selected_base_coefficient_positive_Tor]
  let seen ← liftCoreM <| checkSelectedAndreDependencies roots {}
  unless seen.contains
      ``SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed do
    throwError "Expected existing BS Theorem 7.14 dependency is missing"
  logInfo "Selected coefficient André comparison: only existing BS Theorem 7.14 is permitted."
end

assert_selected_andre_dependencies
