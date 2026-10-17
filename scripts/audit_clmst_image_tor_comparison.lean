import SerrePositivity.CLMST.PerfectoidizationImageTorComparison
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.IsPerfectoidization.mapAlgHom_mapAlgHom
assert_no_sorry SerrePositivity.BhattScholze.perfectoidization_image_factorization
#print axioms SerrePositivity.IsPerfectoidization.mapAlgHom_mapAlgHom
#print axioms SerrePositivity.BhattScholze.perfectoidization_image_factorization
#print axioms SerrePositivity.BhattScholze.perfectoidization_image_ker_coker_annihilated
#print axioms SerrePositivity.BhattScholze.exists_image_perfectoidization_almost_comparison
#print axioms SerrePositivity.CLMST.perfectoidIdeal_TorInput_iff_image
#print axioms SerrePositivity.CLMST.exists_localization_image_perfectoidization_Tor_comparison

noncomputable section
universe u
open SerrePositivity SerrePositivity.CLMST CategoryTheory
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

-- The actual ordinary localization unit supplies the support bound, and one
-- image perfectoidization is selected before all modules, precisions and degrees.
theorem audit_actual_localization_image_all_Tor_tests
    (R A C : Type u) [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Module.Finite R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    let φ := (Algebra.TensorProduct.includeRight : A →ₐ[R] Localization.Away (ρ 0) ⊗[R] A)
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D) (g : φ.range →ₐ[R] D),
      @IsPerfectoidization φ.range D inferInstance inferInstance p inferInstance g.toRingHom ∧
      ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) → ∀ i : ℕ,
        (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
          torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0) ↔
        (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
          torCoefficientScalarEndomorphism D N i (algebraMap R D s) = 0) := by
  let L := Localization.Away (ρ 0)
  let φ : A →ₐ[R] L ⊗[R] A := Algebra.TensorProduct.includeRight
  have hlin : φ.toLinearMap = TensorProduct.mk R L A 1 := rfl
  let : IsLocalizedModule (.powers (ρ 0)) φ.toLinearMap := by
    rw [hlin]
    infer_instance
  exact exists_localization_image_perfectoidization_Tor_comparison
    hR ρ hρ φ hf φ.toLinearMap (LinearMap.id) (LinearMap.id_comp _)

#print axioms audit_actual_localization_image_all_Tor_tests

meta section
open Lean Elab Command
private partial def checkImageDependencies (allowed : NameSet) (todo : List Name)
    (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← checkImageDependencies allowed rest seen
    let seen := seen.insert n
    let some info := (← getEnv).find? n | return ← checkImageDependencies allowed rest seen
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx && !allowed.contains n then
      throwError "Unapproved sorry in image comparison: {n}"
    checkImageDependencies allowed (deps.toList ++ rest) seen

elab "assert_image_comparison_dependencies" : command => do
  let andre := ``SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed
  let integral := ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral
  let _ ← liftCoreM <| checkImageDependencies (({} : NameSet).insert andre)
    [``SerrePositivity.BhattScholze.perfectoidization_image_ker_coker_annihilated,
     ``SerrePositivity.CLMST.perfectoidIdeal_TorInput_iff_image] {}
  let seen ← liftCoreM <| checkImageDependencies ((({} : NameSet).insert andre).insert integral)
    [``SerrePositivity.BhattScholze.exists_image_perfectoidization_almost_comparison,
     ``SerrePositivity.CLMST.exists_localization_image_perfectoidization_Tor_comparison,
     ``audit_actual_localization_image_all_Tor_tests] {}
  unless seen.contains andre && seen.contains integral do
    throwError "Expected existing Andre and B-I dependencies are missing"
  logInfo "Actual image comparisons: only existing BS 7.14 and integral existence B-I are permitted."
end

assert_image_comparison_dependencies
