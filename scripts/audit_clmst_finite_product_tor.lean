import SerrePositivity.CLMST.PerfectoidFiniteProductTor
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.IsIntegralPerfectoid.isPerfectoidization_id
#print axioms SerrePositivity.IsIntegralPerfectoid.isPerfectoidization_id
#print axioms SerrePositivity.BhattScholze.isIntegralPerfectoid_finPi
#print axioms SerrePositivity.BhattScholze.finiteProduct_perfectoidization_exists_algEquiv
#print axioms SerrePositivity.CLMST.finiteProduct_perfectoidization_flat
#print axioms SerrePositivity.CLMST.finiteProduct_perfectoidization_Tor_zero
#print axioms SerrePositivity.CLMST.supported_finiteProduct_image_powerTorsionTorInput
#print axioms SerrePositivity.CLMST.localizationSplitting_exists_finiteProduct_image_TorInput

noncomputable section
universe u
open SerrePositivity SerrePositivity.CLMST CategoryTheory
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

-- Actual common-model maps, the actual image unit, all Tor tests, and precisely
-- the original coefficient scalar are retained together in one existential.
theorem audit_finite_common_model_Tor_and_original_scalar
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers (ρ 0)) L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L)) :
    ∃ E : Subalgebra R (Fin r → L), Module.Finite R E ∧
      ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E),
        (∀ a, E.val (u a) = e ((1 : L) ⊗ₜ[R] a)) ∧
        ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D) (g : v.range →ₐ[R] D),
          @IsPerfectoidization v.range D inferInstance inferInstance p inferInstance g.toRingHom ∧
          (∀ s : R, g (v.rangeRestrict (fun _ => s)) = algebraMap R D s) ∧
          ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
            ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR (ρ 0),
              torCoefficientScalarEndomorphism D N i (algebraMap R D s) = 0 := by
  obtain ⟨E, hE, u, v, hu, _hv, D, hD, hDalg, g, hg, hTor⟩ :=
    localizationSplitting_exists_finiteProduct_image_TorInput hR ρ hρ L r e
  let := hD
  let := hDalg
  refine ⟨E, hE, u, v, hu, D, hD, hDalg, g, hg, ?_, hTor⟩
  intro s
  change g (v.rangeRestrict (algebraMap R (Fin r → R) s)) = algebraMap R D s
  rw [v.rangeRestrict.commutes, g.commutes]

-- Rank zero is admitted by the actual unital image maps; it is never excluded.
theorem audit_rank_zero_image_target_subsingleton
    (R E D : Type u) [CommRing R] [CommRing E] [CommRing D]
    [Algebra R E] [Algebra R D]
    (φ : (Fin 0 → R) →ₐ[R] E) (g : φ.range →ₐ[R] D) : Subsingleton D := by
  let : Subsingleton φ.range := φ.rangeRestrict.toRingHom.codomain_trivial
  exact g.toRingHom.codomain_trivial

assert_no_sorry audit_rank_zero_image_target_subsingleton
#print axioms audit_rank_zero_image_target_subsingleton
#print axioms audit_finite_common_model_Tor_and_original_scalar

meta section
open Lean Elab Command
private partial def checkFiniteProductDependencies (allowed : NameSet) (todo : List Name)
    (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← checkFiniteProductDependencies allowed rest seen
    let seen := seen.insert n
    let some info := (← getEnv).find? n | return ← checkFiniteProductDependencies allowed rest seen
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx && !allowed.contains n then
      throwError "Unapproved sorry in finite-product Tor input: {n}"
    checkFiniteProductDependencies allowed (deps.toList ++ rest) seen

elab "assert_finite_product_Tor_dependencies" : command => do
  let andre := ``SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed
  let integral := ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral
  let onlyIntegral : NameSet := ({} : NameSet).insert integral
  let _ ← liftCoreM <| checkFiniteProductDependencies onlyIntegral
    [``SerrePositivity.BhattScholze.isIntegralPerfectoid_finPi,
     ``SerrePositivity.BhattScholze.finiteProduct_perfectoidization_exists_algEquiv,
     ``SerrePositivity.CLMST.finiteProduct_perfectoidization_flat,
     ``SerrePositivity.CLMST.finiteProduct_perfectoidization_Tor_zero] {}
  let seen ← liftCoreM <| checkFiniteProductDependencies (onlyIntegral.insert andre)
    [``SerrePositivity.CLMST.supported_finiteProduct_image_powerTorsionTorInput,
     ``SerrePositivity.CLMST.localizationSplitting_exists_finiteProduct_image_TorInput,
     ``audit_finite_common_model_Tor_and_original_scalar] {}
  unless seen.contains andre && seen.contains integral do
    throwError "Expected existing Andre and B-I dependencies are missing"
  logInfo "Actual finite-product image Tor: only existing B-I and BS 7.14 are permitted."
end

assert_finite_product_Tor_dependencies
