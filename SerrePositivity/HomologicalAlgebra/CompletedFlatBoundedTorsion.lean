module

public import SerrePositivity.CommutativeAlgebra.BoundedPowerTorsionQuotient
public import SerrePositivity.HomologicalAlgebra.CompletedFlatRegularModule
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedModuleShortExact

/-! # 有界 torsion 加群の完全平坦な完備導来底変換

元の共通指数を保ったまま、実完備導来底変換の離散性と H⁰ の torsion 有界性を得る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B) (a : R)

/-- 有界な冪 torsion を持つ加群の実完備底変換は離散で、同じ指数が H⁰ にも通用する。 -/
theorem completedBaseChange_bounded_torsion_pure
    (hB : IsCompletelyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (M : ModuleCat.{u} R) (N : ℕ)
    (hM : ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0) :
    let Y := (derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
    Y.IsGE 0 ∧ Y.IsLE 0 ∧
      ∀ n : ℕ, ∀ x : (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj Y,
        (φ a) ^ n • x = 0 → (φ a) ^ N • x = 0 := by
  let K := (a ^ N • (LinearMap.id : M →ₗ[R] M)).ker
  let S := ModuleCat.shortComplexOfCompEqZero K.subtype K.mkQ
    (LinearMap.exact_subtype_mkQ K).linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_subtype_mkQ K) K.injective_subtype K.mkQ_surjective
  have hK : ∀ x : S.X₁, a ^ N • x = 0 := fun x => Subtype.ext x.property
  let eK := completedBaseChangePowerTorsionIso φ a hB S.X₁ N hK
  have : ((moduleObjectFunctor B).obj ((ModuleCat.extendScalars φ).obj S.X₁)).IsGE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat B) 0).obj _).IsGE 0
    infer_instance
  have : ((moduleObjectFunctor B).obj ((ModuleCat.extendScalars φ).obj S.X₁)).IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat B) 0).obj _).IsLE 0
    infer_instance
  have h₁ : ((derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj
        (boundedAboveDerivedSingleFunctor.obj S.X₁)).obj).IsGE 0 ∧
      ((derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj
        (boundedAboveDerivedSingleFunctor.obj S.X₁)).obj).IsLE 0 :=
    ⟨DerivedCategory.TStructure.t.isGE_of_iso eK.symm 0,
      DerivedCategory.TStructure.t.isLE_of_iso eK.symm 0⟩
  have h₃ := completedBaseChange_regular_module_pure φ a hB S.X₃
    (isSMulRegular_quotient_pow_kernel a N hM)
  have hp := completedBaseChangeModule_shortExact_pure φ a S hS h₁ ⟨h₃.1, h₃.2.1⟩
  refine ⟨hp.1, hp.2, ?_⟩
  let T := completedModuleShortExactTriangle φ a S hS
  have hd := completedModuleShortExactTriangle_distinguished φ a S hS
  let H := DerivedCategory.homologyFunctor (ModuleCat B) 0
  let eH : H.obj T.obj₁ ≅ (ModuleCat.extendScalars φ).obj S.X₁ :=
    H.mapIso eK ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0).app _
  have hTK (x : H.obj T.obj₁) : (φ a) ^ N • x = 0 := by
    apply eH.toLinearEquiv.injective
    rw [map_smul, map_zero]
    exact extendScalars_pow_smul_zero φ a S.X₁ N hK (eH.hom x)
  have hex := DerivedCategory.HomologySequence.exact₂ T hd 0
  change ∀ n : ℕ, ∀ x : H.obj T.obj₂,
    (φ a) ^ n • x = 0 → (φ a) ^ N • x = 0
  intro n x hx
  have hy : (H.map T.mor₂).hom x = 0 := by
    have hn : Function.Injective (fun y : H.obj T.obj₃ => (φ a) ^ n • y) :=
      (show IsSMulRegular (H.obj T.obj₃) (φ a) from h₃.2.2).pow n
    apply hn
    simp only [smul_zero]
    rw [← map_smul, hx, map_zero]
  have hxrange : x ∈ LinearMap.range (H.map T.mor₁).hom := by
    rw [hex.moduleCat_range_eq_ker]
    exact hy
  obtain ⟨y, rfl⟩ := hxrange
  rw [← map_smul, hTK, map_zero]

end SerrePositivity
