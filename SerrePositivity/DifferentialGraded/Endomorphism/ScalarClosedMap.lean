module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleHom
public import SerrePositivity.DifferentialGraded.Module.HomFunctor

/-! # 実際のHom係数変更比較と閉零加群射の一致 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

lemma scalarHomComparison_closedMap {K L : Complex A} (f : K ⟶ L) :
    (ScalarExtension.unitIso φ).inv ≫ (ScalarExtension.extension φ).map (closedMap A f) ≫
        ScalarExtension.homComparison φ K L =
      closedMap A' ((ScalarExtension.extension φ).map f) := by
  let := φ.toAlgebra
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (ScalarExtension.homComparison φ K L).f 0
    (((ScalarExtension.extension φ).map (closedMap A f)).f 0
      ((ScalarExtension.unitIso φ).inv.f 0
        ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A'))).inv (1 : A')))) = _
  erw [ScalarExtension.sphereIso_inv_one φ 0, ModuleCat.ExtendScalars.map_tmul φ]
  have hc : (closedMap A f).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) = Cochain.ofHom f :=
    closedMap_cycle A f
  rw [hc]
  change (ScalarExtension.homComparison φ K L).f 0 ((1 : A') ⊗ₜ[A] Cochain.ofHom f) =
    (cycleFromUnit _ (closedMap A' ((ScalarExtension.extension φ).map f))).val
  rw [closedMap_cycle]
  apply Cochain.ext₀
  intro i
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((ScalarExtension.homComparison φ K L).f 0 ((1 : A') ⊗ₜ[A] Cochain.ofHom f)).v
      i i (add_zero i) ((1 : A') ⊗ₜ[A] x) =
    ((ScalarExtension.extension φ).map f).f i ((1 : A') ⊗ₜ[A] x)
  erw [ScalarExtension.homComparison_apply φ K L 0 i i (add_zero i)]
  rfl

variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHom_closedMap {M N : ModuleCategory A D} (f : M ⟶ N) :
    (ScalarExtension.unitIso φ).inv ≫
        (ScalarExtension.extension φ).map (ForgetEnrichment.homTo (Complex A) f) ≫
        scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
          (ForgetEnrichment.to (Complex A) N) =
      ForgetEnrichment.homTo (Complex A') ((ScalarExtension.moduleExtension φ D).map f) := by
  apply moduleHom_ext
  intro x
  rw [Category.assoc, Category.assoc, scalarModuleHom_π,
    ← CategoryTheory.Functor.map_comp_assoc, ← moduleEvaluation_closedMap]
  have hx := moduleEvaluation_closedMap A' (ScalarExtension.DGBaseChange φ D) x
    ((ScalarExtension.moduleExtension φ D).map f)
  rw [ScalarExtension.moduleExtension_eval] at hx
  exact (scalarHomComparison_closedMap φ ((moduleEvaluation A D x).map f)).trans hx

end SerrePositivity.DifferentialGraded
