module

public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensorAugmentation
public import SerrePositivity.HomologicalAlgebra.AlgebraScalarExtensionModule
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAlgebraAugmentation

/-! # 元の通常 tensor への係数正規化と標準 augmentation

係数環を左因子に置き、環代数の元とその標準写像を保つ。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory MonoidalCategory DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R B S : Type u) [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S]

/-- 底変換の通常加群を、元の R 作用を持つ通常 tensor へ正規化する。 -/
def algebraBaseChangeModuleNormalizationIso :
    (ModuleCat.restrictScalars (algebraMap R B)).obj
      ((ModuleCat.extendScalars (algebraMap R B)).obj (ModuleCat.of R S)) ≅
      ModuleCat.of R (B ⊗[R] S) :=
  (extendRestrictTensorIso (algebraMap R B)).app (ModuleCat.of R S) ≪≫
    (TensorProduct.congr (algebraSelfRestrictionIso R B).toLinearEquiv
      (LinearEquiv.refl R S)).toModuleIso

/-- 正規化の実写像は通常 tensor の左因子の標準比較。 -/
theorem algebraBaseChangeModuleNormalizationIso_hom :
    (algebraBaseChangeModuleNormalizationIso R B S).hom =
      (extendRestrictTensorIso (algebraMap R B)).hom.app (ModuleCat.of R S) ≫
        ((algebraSelfRestrictionIso R B).hom ⊗ₘ 𝟙 (ModuleCat.of R S)) := rfl

/-- R 線形正規化と元の B 線形正規化は、全ての tensor の元で同じ写像。 -/
theorem algebraBaseChangeModuleNormalizationIso_apply
    (x : (ModuleCat.extendScalars (algebraMap R B)).obj (ModuleCat.of R S)) :
    (algebraBaseChangeModuleNormalizationIso R B S).hom x =
      (algebraScalarExtensionModuleIso R B (ModuleCat.of R S)).hom x := by
  induction x using TensorProduct.inductionOn with
  | tmul b s => rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- 元の係数作用で正規化した、実底変換と実導来 tensor の比較。 -/
def algebraDerivedBaseChangeTensorIso :
    (derivedRestrictScalars (algebraMap R B)).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj ≅
      (boundedAboveDerivedTensorAlgebra (R := R) B S).X.obj :=
  DerivedCategory.Minus.ι.mapIso
    (boundedAboveDerivedBaseChangeTensorIso (algebraMap R B)
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S)) ≪≫
    boundedAboveDerivedTensor.mapIso (Iso.prod
      (boundedAboveDerivedSingleFunctor.mapIso (algebraSelfRestrictionIso R B))
      (Iso.refl (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S)))))

/-- 元の通常環 tensor への正規化後も、底変換と tensor の augmentation は一致する。 -/
theorem algebraDerivedBaseChangeTensorIso_augmentation :
    (derivedRestrictScalars (algebraMap R B)).map
        ((boundedAboveDerivedBaseChangeModuleAugmentation (algebraMap R B)).app
          (ModuleCat.of R S)) ≫
      (derivedRestrictScalarsSingleIso (algebraMap R B) 0).hom.app
        ((ModuleCat.extendScalars (algebraMap R B)).obj (ModuleCat.of R S)) ≫
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map
        (algebraBaseChangeModuleNormalizationIso R B S).hom =
    (algebraDerivedBaseChangeTensorIso R B S).hom ≫
      (boundedAboveDerivedTensorAlgebraAugmentation (R := R) B S).hom.hom.hom := by
  let M := ModuleCat.of R S
  let e := boundedAboveDerivedBaseChangeTensorIso (algebraMap R B)
    (boundedAboveDerivedSingleFunctor.obj M)
  let t := (algebraSelfRestrictionIso R B).hom ⊗ₘ 𝟙 M
  have hraw := boundedAboveDerivedBaseChangeTensorIso_augmentation (algebraMap R B) M
  have hn := boundedAboveDerivedTensorModuleAugmentation_naturality
    (algebraSelfRestrictionIso R B).hom (𝟙 M)
  rw [boundedAboveDerivedSingleFunctor.map_id] at hn
  have he : (algebraDerivedBaseChangeTensorIso R B S).hom = e.hom.hom ≫
      (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
        (boundedAboveDerivedSingleFunctor.map (algebraSelfRestrictionIso R B).hom)
        (𝟙 (boundedAboveDerivedSingleFunctor.obj M)))).hom := rfl
  rw [boundedAboveDerivedTensorAlgebraAugmentation_hom]
  calc
    _ = e.hom.hom ≫
        (boundedAboveDerivedTensorModuleAugmentation
          (baseChangeScalarModule (algebraMap R B))).app M ≫
        (DerivedCategory.singleFunctor (ModuleCat R) 0).map t := by
      simpa only [algebraBaseChangeModuleNormalizationIso_hom, Functor.map_comp, Category.assoc]
        using congrArg (fun k => k ≫ (DerivedCategory.singleFunctor (ModuleCat R) 0).map t) hraw
    _ = _ := by
      rw [he, Category.assoc, hn]

end SerrePositivity
