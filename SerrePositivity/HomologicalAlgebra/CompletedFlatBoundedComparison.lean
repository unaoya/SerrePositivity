module

public import SerrePositivity.HomologicalAlgebra.CompletedFlatBoundedTorsion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure

/-! # 有界 torsion と通常 tensor への標準比較

通常 tensor が導来完備である場合、完備導来 tensor はその single 対象と同型になる。
比較は元の標準 augmentation から構成し、任意の同型を選ばない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B) (a : R)

/-- 通常 tensor の導来完備性の下で、元の標準 augmentation の完備化は同型。 -/
theorem completedBaseChange_bounded_augmentation_isIso
    (hB : IsCompletelyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (M : ModuleCat.{u} R) (N : ℕ)
    (hM : ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0)
    (hL : IsModuleComplete B (φ a) ((ModuleCat.extendScalars φ).obj M)) :
    IsIso ((derivedComplexCompletionFunctor B (φ a)).map
      ((boundedAboveDerivedBaseChangeModuleAugmentation φ).app M)) := by
  let X := ((boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
  let L := (DerivedCategory.singleFunctor (ModuleCat B) 0).obj ((ModuleCat.extendScalars φ).obj M)
  let F := derivedComplexCompletionFunctor B (φ a)
  let f : X ⟶ L := (boundedAboveDerivedBaseChangeModuleAugmentation φ).app M
  let H := DerivedCategory.homologyFunctor (ModuleCat B) 0
  have hp := completedBaseChange_bounded_torsion_pure φ a hB M N hM
  have : (F.obj X).IsGE 0 := hp.1
  have : (F.obj X).IsLE 0 := hp.2.1
  have : (boundedAboveDerivedSingleFunctor.obj M).obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj M).IsLE 0
    infer_instance
  have : X.IsLE 0 := boundedAboveLeftDerived_isLE (ModuleCat.extendScalars φ)
    (boundedAboveDerivedSingleFunctor.obj M) 0
  have : L.IsLE 0 := by dsimp [L]; infer_instance
  have hf : IsIso (H.map f) := by
    have hc : IsIso (H.map f ≫ (realizedSingleH0Iso B).hom.app
        ((ModuleCat.extendScalars φ).obj M)) := by
      rw [boundedAboveDerivedBaseChangeModuleAugmentation_homology]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((realizedSingleH0Iso B).hom.app ((ModuleCat.extendScalars φ).obj M))
  have hF : IsIso (H.map (F.map f)) :=
    derivedComplexCompletion_h0_map_isIso B (φ a) f inferInstance inferInstance hf
  let eL : L ≅ F.obj L := derivedComplexCompletionUnitIso B (φ a) L hL
  apply (DerivedCategory.isIso_iff (ModuleCat B) _).mpr
  intro i
  by_cases hi : i = 0
  · subst i
    exact hF
  · have hx : IsZero ((DerivedCategory.homologyFunctor (ModuleCat B) i).obj (F.obj X)) := by
      by_cases hpos : 0 < i
      · exact DerivedCategory.isZero_of_isLE _ 0 i hpos
      · exact DerivedCategory.isZero_of_isGE _ 0 i (by omega)
    have hl := (derivedSingleHomology_isZero ((ModuleCat.extendScalars φ).obj M) i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat B) i).mapIso eL.symm)
    exact hx.isIso hl _

/-- 元の完備底変換を通常 tensor へ同定する標準比較。 -/
def completedBaseChangeBoundedAugmentationIso
    (hB : IsCompletelyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (M : ModuleCat.{u} R) (N : ℕ)
    (hM : ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0)
    (hL : IsModuleComplete B (φ a) ((ModuleCat.extendScalars φ).obj M)) :
    (derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedSingleFunctor.obj M)).obj ≅
        (moduleObjectFunctor B).obj ((ModuleCat.extendScalars φ).obj M) := by
  have := completedBaseChange_bounded_augmentation_isIso φ a hB M N hM hL
  exact asIso ((derivedComplexCompletionFunctor B (φ a)).map
      ((boundedAboveDerivedBaseChangeModuleAugmentation φ).app M)) ≪≫
    (derivedComplexCompletionUnitIso B (φ a) _ hL).symm

/-- bounded torsion の比較は、元の augmentation を完備化の単位に沿って延長する。 -/
theorem completedBaseChangeBoundedAugmentationIso_unit
    (hB : IsCompletelyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (M : ModuleCat.{u} R) (N : ℕ)
    (hM : ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0)
    (hL : IsModuleComplete B (φ a) ((ModuleCat.extendScalars φ).obj M)) :
    (derivedComplexCompletionUnit B (φ a)).app
        ((boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedSingleFunctor.obj M)).obj ≫
      (completedBaseChangeBoundedAugmentationIso φ a hB M N hM hL).hom =
        (boundedAboveDerivedBaseChangeModuleAugmentation φ).app M := by
  let f := (boundedAboveDerivedBaseChangeModuleAugmentation φ).app M
  let e := derivedComplexCompletionUnitIso B (φ a)
    ((moduleObjectFunctor B).obj ((ModuleCat.extendScalars φ).obj M)) hL
  change _ ≫ ((derivedComplexCompletionFunctor B (φ a)).map f ≫ e.inv) = f
  rw [← Category.assoc]
  erw [← (derivedComplexCompletionUnit B (φ a)).naturality f]
  change (f ≫ e.hom) ≫ e.inv = f
  simp

/-- 通常 tensor が導来完備なら、同じ共通指数を持ち古典的にも完備となる。 -/
theorem isAdicComplete_extendScalars_of_bounded_torsion
    (hB : IsCompletelyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (M : ModuleCat.{u} R) (N : ℕ)
    (hM : ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0)
    (hL : IsModuleComplete B (φ a) ((ModuleCat.extendScalars φ).obj M)) :
    IsAdicComplete (Ideal.span {φ a}) ((ModuleCat.extendScalars φ).obj M) := by
  let e := completedBaseChangeBoundedAugmentationIso φ a hB M N hM hL
  let H := DerivedCategory.homologyFunctor (ModuleCat B) 0
  let eH := H.mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0).app _
  have hp := completedBaseChange_bounded_torsion_pure φ a hB M N hM
  apply isAdicComplete_of_isModuleComplete_of_bounded_torsion B (φ a) _ hL
  refine ⟨N, fun n x hx => ?_⟩
  have hx' : (φ a) ^ n • eH.inv x = 0 := by
    rw [← map_smul, hx, map_zero]
  have hz := hp.2.2 n (eH.inv x) hx'
  have he := congrArg (fun z => eH.hom z) hz
  change eH.toLinearEquiv ((φ a) ^ N • eH.toLinearEquiv.symm x) = eH.toLinearEquiv 0 at he
  simpa only [map_smul, LinearEquiv.apply_symm_apply, map_zero] using he

end SerrePositivity
