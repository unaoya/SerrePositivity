module
public import SerrePositivity.DifferentialGraded.Morita.KernelResolutionModel

/-! # kernel射に対する計算同型と増大比較の自然性

## 概要
入力の解像度計算と通常tensorへの増大比較を、kernelの射について整合させる。

## 方針
H⁰計算の自然性と既存の主導来kernel射の定義を用い、同じ解像度族の比較を証明する。

## 規約と注意
任意可換環・独立宇宙。局所Hom K-flat条件は不要。

## 使われ方
U16aの合成比較をkernel射に自然な族にまとめるための計算API。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  {P P' : BimoduleCategory A E D} (f : P ⟶ P')

/-- H⁰計算同型は、任意の通常kernel射に自然。 -/
lemma kernelTensorHomotopyComputation_kernel_naturality (M : ModuleCategory A D) :
    (moduleHomotopyToDerivedClosed A E).map
        ((kernelTensorHomotopyMap A D E f).app ((moduleToHomotopy A D).obj M)) ≫
        (kernelTensorHomotopyComputation A D E (BimoduleCategory.underlying A E D P') M).hom =
      (kernelTensorHomotopyComputation A D E (BimoduleCategory.underlying A E D P) M).hom ≫
        (moduleToDerived A E).map ((kernelTensorMap A D E f).app M) := by
  have h := (moduleToHomotopyDerivedIso A E).hom.naturality
    ((kernelTensorMap A D E f).app M)
  simp only [Functor.comp_map] at h
  simp only [kernelTensorHomotopyComputation, Iso.trans_hom, Functor.mapIso_hom,
    kernelTensorHomotopyMap_app, eqToIso_refl, Iso.refl_hom,
    CategoryTheory.Functor.map_id, Iso.app_hom]
  erw [Category.id_comp, Category.id_comp]
  exact h

/-- 任意指定解像度の計算同型はkernel射について自然。 -/
lemma kernelResolutionDerivedTensorComputation_kernel_naturality
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (M : ModuleCategory A D) :
    (kernelResolutionDerivedTensorMap A D E R f).app ((moduleToDerived A D).obj M) ≫
        (kernelResolutionDerivedTensorComputation A D E
          (BimoduleCategory.underlying A E D P') R M).hom =
      (kernelResolutionDerivedTensorComputation A D E
          (BimoduleCategory.underlying A E D P) R M).hom ≫
        (moduleToDerived A E).map ((kernelTensorMap A D E f).app (R M).obj) := by
  have h := (whiskerRight (kernelTensorHomotopyMap A D E f)
    (moduleHomotopyToDerivedClosed A E)).naturality
    (moduleDerivedResolutionComputation A D R M).hom
  dsimp only [Functor.comp_map] at h
  dsimp only [kernelResolutionDerivedTensorComputation, Iso.trans_hom,
    Functor.mapIso_hom]
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc]
  erw [← h]
  rw [Category.assoc]
  dsimp only [whiskerRight_app]
  erw [kernelTensorHomotopyComputation_kernel_naturality A D E f (R M).obj]
  rw [Category.assoc]
  rfl

/-- 解像度から通常tensorへの増大比較はkernel射に自然。 -/
lemma kernelDerivedTensorAugmentation_kernel_naturality (M : ModuleCategory A D) :
    (kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D) f).app
        ((moduleToDerived A D).obj M) ≫
        (kernelDerivedTensorAugmentation A D E (BimoduleCategory.underlying A E D P')).app M =
      (kernelDerivedTensorAugmentation A D E (BimoduleCategory.underlying A E D P)).app M ≫
        (moduleToDerived A E).map ((kernelTensorMap A D E f).app M) := by
  rw [kernelDerivedTensorAugmentation_app, kernelDerivedTensorAugmentation_app]
  rw [← Category.assoc, kernelResolutionDerivedTensorComputation_kernel_naturality]
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun k =>
    (kernelResolutionDerivedTensorComputation A D E (BimoduleCategory.underlying A E D P)
      (moduleCanonicalProjectiveResolution A D) M).hom ≫ (moduleToDerived A E).map k)
    ((kernelTensorMap A D E f).naturality (moduleCanonicalProjectiveResolution A D M).π).symm

/-- 解像度tensorモデルのkernel変数に関する自然変換。 -/
def kernelResolutionTensorModelMap
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    kernelResolutionTensorModelFunctor A D E (BimoduleCategory.underlying A E D P) R ⟶
      kernelResolutionTensorModelFunctor A D E (BimoduleCategory.underlying A E D P') R where
  app M := (moduleToDerived A E).map ((kernelTensorMap A D E f).app (R M).obj)
  naturality {M N} g := by
    rw [kernelResolutionTensorModelFunctor_map, kernelResolutionTensorModelFunctor_map]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (moduleToDerived A E).map
      ((kernelTensorMap A D E f).naturality ((R M).lift (R N) g))

/-- 解像度モデルの比較はkernel射にも自然。 -/
lemma kernelResolutionTensorModelIso_kernel_naturality
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    whiskerLeft (moduleToDerived A D) (kernelResolutionDerivedTensorMap A D E R f) ≫
        (kernelResolutionTensorModelIso A D E (BimoduleCategory.underlying A E D P') R).hom =
      (kernelResolutionTensorModelIso A D E (BimoduleCategory.underlying A E D P) R).hom ≫
        kernelResolutionTensorModelMap A D E f R := by
  apply NatTrans.ext
  funext M
  have h := kernelResolutionDerivedTensorComputation_kernel_naturality A D E f R M
  simp only [kernelResolutionDerivedTensorComputation, Iso.trans_hom, Functor.mapIso_hom,
    moduleDerivedResolutionComputation, Iso.app_hom] at h
  simp only [NatTrans.comp_app, whiskerLeft_app, kernelResolutionTensorModelMap,
    kernelResolutionTensorModelIso, Iso.trans_hom, whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.isoCopyObj_hom_app]
  erw [Category.id_comp, Category.id_comp]
  exact h

end SerrePositivity.DifferentialGraded.Morita
