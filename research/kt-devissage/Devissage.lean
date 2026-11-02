module
public import SerrePositivity.KTheory.DevissageRestriction

/-! # G₀ dévissage for arbitrary closed supports -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits
open scoped ModuleCat.Algebra
variable {R : Type u} [CommRing R] [IsNoetherianRing R] (J : Ideal R)

/-- Restricting the sum of filtration factors recovers the original supported class. -/
lemma DevissageFlag.restriction_value {M : ModuleCat.{u} R} (F : DevissageFlag J M) :
    ∀ [Module.Finite R M] (hs : Module.support R M ⊆ supportZeroLocus J),
      quotientG0ToSupported J F.value =
        G0WithSupport.mk (⟨M, inferInstance, hs⟩ : SupportedFGModuleOn (supportZeroLocus J)) := by
  induction F with
  | @zero M hz =>
    intro _ hs
    have : Subsingleton M := ModuleCat.subsingleton_of_isZero hz
    exact (map_zero _).trans (G0WithSupport.mk_of_subsingleton _).symm
  | @step M U h rest ih =>
    intro _ hs
    let X : SupportedFGModuleOn (supportZeroLocus J) := ⟨M, inferInstance, hs⟩
    let L : SupportedFGModuleOn (supportZeroLocus J) :=
      ⟨ModuleCat.of R U, finiteModuleSupportedOn.submodule X.property U⟩
    let Q : SupportedFGModuleOn (supportZeroLocus J) :=
      ⟨ModuleCat.of R (M ⧸ U), finiteModuleSupportedOn.quotient X.property U⟩
    let E : SupportedModuleShortExact (supportZeroLocus J) :=
      { left := L
        middle := X
        right := Q
        f := U.subtype
        g := U.mkQ
        injective := Subtype.val_injective
        exact := LinearMap.exact_iff.mpr (by rw [Submodule.ker_mkQ, Submodule.range_subtype])
        surjective := U.mkQ_surjective }
    have hL : quotientG0ToSupported J rest.value = G0WithSupport.mk L := ih L.property.2
    have hQ := quotientG0ToSupported_annihilatedClass J Q h
    change quotientG0ToSupported J (rest.value +
      annihilatedClass J (ModuleCat.of R (M ⧸ U)) h) = G0WithSupport.mk X
    rw [map_add, hL]
    change quotientG0ToSupported J (annihilatedClass J (ModuleCat.of R (M ⧸ U)) h) =
      G0WithSupport.mk Q at hQ
    rw [hQ]
    exact (G0WithSupport.mk_shortExact E).symm

lemma quotientG0ToSupported_devissageInverse :
    (quotientG0ToSupported J).comp (devissageInverse J) =
      AddMonoidHom.id (G0WithSupport (supportZeroLocus J)) := by
  apply G0WithSupport.hom_ext
  intro M
  have := M.property.1
  change quotientG0ToSupported J (devissageInverse J (G0WithSupport.mk M)) = _
  rw [devissageInverse_mk]
  exact (chosenDevissageFlag J M).restriction_value J M.property.2

lemma devissageInverse_quotientG0ToSupported :
    (devissageInverse J).comp (quotientG0ToSupported J) = AddMonoidHom.id (G0 (R ⧸ J)) := by
  apply G0WithSupport.hom_ext
  intro M
  have := (quotientSupportedModule J M).property.1
  change devissageInverse J (quotientG0ToSupported J (G0WithSupport.mk M)) = _
  rw [quotientG0ToSupported_mk, devissageInverse_mk]
  change (chosenDevissageFlag J (quotientSupportedModule J M)).value = G0WithSupport.mk M
  rw [DevissageFlag.value_of_annihilated _ (quotientModule_annihilator J M.obj)]
  exact G0WithSupport.mk_iso (quotientAnnihilatedIso J M)

/-- Finite modules on V(J) and finite R/J modules have canonically isomorphic G₀ groups.
No regularity, finite projective dimension, or reducedness of J is required. -/
def g0QuotientDevissageEquiv : G0 (R ⧸ J) ≃+ G0WithSupport (supportZeroLocus J) where
  toFun := quotientG0ToSupported J
  invFun := devissageInverse J
  left_inv x := DFunLike.congr_fun (devissageInverse_quotientG0ToSupported J) x
  right_inv x := DFunLike.congr_fun (quotientG0ToSupported_devissageInverse J) x
  map_add' := map_add _
end SerrePositivity
