module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.BoundedProjectiveKFlat
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.NativeScalarModelAugmentation
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeAugmentationModels

/-!
# 元の加群での非有界・上に有界な導来底変換の照合

## 概要
同じ元の加群の射影分解を使い、二つの導来底変換と元の増大を照合する。

## 方針
元の射影分解の整数次数への延長を両方の模型に使い、元の厳密な増大の自然性を保つ。

## 規約
同型を射から逆算して定義しない。元の指定された射影模型の二つの計算同型を合成する。

## 使われ方
元の剰余行の指定同型を、元の非有界な分解のκの各項と照合する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DifferentialGraded.ScalarExtension HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元の加群の同じ射影分解による、非有界・上に有界な標準底変換の同型。 -/
def unboundedBoundedModuleBaseChangeIso (f : R →+* S) (M : ModuleCat.{u} R) :
    (complexDerivedExtension f).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ≅
      ((boundedAboveDerivedBaseChange f).obj (boundedAboveDerivedSingleFunctor.obj M)).obj := by
  let P := projectiveResolutionDerivedModel (projectiveResolution M)
  let ε := projectiveResolutionCochainAugmentation (projectiveResolution M)
  exact nativeDerivedScalarModelIso f ε inferInstance (boundedAboveDerivedModel_kFlat P) ≪≫
    (boundedAboveDerivedBaseChangeModelIso f (boundedAboveDerivedSingleFunctor.obj M) P).symm

/-- 同じ元の加群の射を、両方の元の標準底変換で保つ。 -/
@[reassoc] theorem unboundedBoundedModuleBaseChangeIso_naturality (f : R →+* S)
    {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    (complexDerivedExtension f).map ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map g) ≫
        (unboundedBoundedModuleBaseChangeIso f N).hom =
      (unboundedBoundedModuleBaseChangeIso f M).hom ≫
        ((boundedAboveDerivedBaseChange f).map (boundedAboveDerivedSingleFunctor.map g)).hom := by
  let P := projectiveResolution M
  let Q := projectiveResolution N
  let PM := projectiveResolutionDerivedModel P
  let PN := projectiveResolutionDerivedModel Q
  let εP := projectiveResolutionCochainAugmentation P
  let εQ := projectiveResolutionCochainAugmentation Q
  let h := extLift P g Q
  let aM := nativeDerivedScalarModelIso f εP inferInstance (boundedAboveDerivedModel_kFlat PM)
  let aN := nativeDerivedScalarModelIso f εQ inferInstance (boundedAboveDerivedModel_kFlat PN)
  let bM := boundedAboveDerivedBaseChangeModelIso f (boundedAboveDerivedSingleFunctor.obj M) PM
  let bN := boundedAboveDerivedBaseChangeModelIso f (boundedAboveDerivedSingleFunctor.obj N) PN
  have hp : DerivedCategory.Q.map h ≫ PN.iso.hom = PM.iso.hom ≫
      (boundedAboveDerivedSingleFunctor.map g).hom := by
    change DerivedCategory.Q.map (extLift P g Q) ≫ DerivedCategory.Q.map εQ =
      DerivedCategory.Q.map εP ≫ DerivedCategory.Q.map
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map g)
    rw [← Functor.map_comp, ← Functor.map_comp, projectiveResolutionCochainAugmentation_naturality]
  have hB := boundedAboveLeftDerivedModelIso_naturality (ModuleCat.extendScalars f) PM PN
    (boundedAboveDerivedSingleFunctor.map g) h hp
  change ((boundedAboveDerivedBaseChange f).map (boundedAboveDerivedSingleFunctor.map g)).hom ≫
      bN.hom = bM.hom ≫ DerivedCategory.Q.map
        (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map h) at hB
  have hA := nativeDerivedScalarModelIso_naturality f εP inferInstance
    (boundedAboveDerivedModel_kFlat PM) εQ inferInstance (boundedAboveDerivedModel_kFlat PN)
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map g) h
    (projectiveResolutionCochainAugmentation_naturality g P Q).symm
  apply (cancel_mono bN.hom).mp
  change ((complexDerivedExtension f).map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map g) ≫
      (aN.hom ≫ bN.inv)) ≫ bN.hom =
    ((aM.hom ≫ bM.inv) ≫
      ((boundedAboveDerivedBaseChange f).map (boundedAboveDerivedSingleFunctor.map g)).hom) ≫ bN.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [hB]
  simp only [Iso.inv_hom_id_assoc]
  exact hA

/-- 元の同じ加群図式での、二つの標準底変換の自然同型。 -/
def unboundedBoundedModuleBaseChangeNatIso (f : R →+* S) :
    DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙ complexDerivedExtension f ≅
      boundedAboveDerivedSingleFunctor ⋙ boundedAboveDerivedBaseChange f ⋙ DerivedCategory.Minus.ι :=
  NatIso.ofComponents (unboundedBoundedModuleBaseChangeIso f)
    (fun g => unboundedBoundedModuleBaseChangeIso_naturality f g)

/-- 元の加群の比較は、元の通常係数拡大への同じ増大を保つ。 -/
@[reassoc] theorem unboundedBoundedModuleBaseChangeIso_augmentation (f : R →+* S)
    (M : ModuleCat.{u} R) :
    (unboundedBoundedModuleBaseChangeIso f M).hom ≫
        (boundedAboveDerivedBaseChangeModuleAugmentation f).app M =
      (complexDerivedExtensionAugmentation f).app
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) ≫
        DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.extendScalars f) (.up ℤ) 0).hom.app M) := by
  let PM := projectiveResolutionDerivedModel (projectiveResolution M)
  let ε := projectiveResolutionCochainAugmentation (projectiveResolution M)
  let a := nativeDerivedScalarModelIso f ε inferInstance (boundedAboveDerivedModel_kFlat PM)
  let b := boundedAboveDerivedBaseChangeModelIso f (boundedAboveDerivedSingleFunctor.obj M) PM
  have hB := boundedAboveDerivedBaseChangeModuleAugmentation_projective_models f PM ε rfl
  change (boundedAboveDerivedBaseChangeModuleAugmentation f).app M = b.hom ≫
    DerivedCategory.Q.map (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map ε ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.extendScalars f) (.up ℤ) 0).hom.app M) at hB
  have hA := nativeDerivedScalarModelIso_comp_augmentation f ε inferInstance
    (boundedAboveDerivedModel_kFlat PM)
  change (a.hom ≫ b.inv) ≫ (boundedAboveDerivedBaseChangeModuleAugmentation f).app M = _
  erw [hB]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
      (ModuleCat.extendScalars f) (.up ℤ) 0).hom.app M)) hA

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
