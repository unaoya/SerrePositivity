module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceIdentityAugmentation
public import Mathlib.Data.ZMod.Basic

/-! # 作用の恒等・合成比較と増大の監査

## 概要
実際の恒等・合成比較が通常tensorの同じ図式を計算することを独立宇宙で検査する。

## 方針
合成の増大squareと恒等比較の成分計算を直接使い、各公開補題の公理を出力する。

## 規約と注意
単位・結合の全導来coherenceの受入とは区別する。新しい比較を選び直さない。

## 使われ方
U16aの作用coherenceを通常bimodule図式へ帰着する計算入口。
-/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.Morita
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]

example (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimoduleIdentityIso A D).hom.app ((moduleToDerived A D).obj M) =
      (kernelDerivedTensorAugmentation A D D (Bimodule.diagonal A D)).app M ≫
        (moduleToDerived A D).map ((kernelIdentityClosedIso A D).hom.app M) :=
  kernelDerivedTensorOnBimoduleIdentityIso_augmentation A D M

example (P : Bimodule A E D) (Q : Bimodule A F E)
    (hP : Bimodule.rightRelativeKFlat A E D P) (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimoduleCompositionIso A D E F P Q hP).hom.app
        ((moduleToDerived A D).obj M) ≫
      (kernelDerivedTensorAugmentation A D F (BimoduleTensor.compose A F E D Q P)).app M =
    (kernelDerivedTensorOnBimodule A E F Q).map
        ((kernelDerivedTensorAugmentation A D E P).app M) ≫
      (kernelDerivedTensorAugmentation A E F Q).app ((kernelTensor A D E P).onClosed.obj M) ≫
        (moduleToDerived A F).map ((kernelTensorCompositionClosedIso A D E F P Q).hom.app M) :=
  kernelDerivedTensorOnBimoduleCompositionIso_augmentation A D E F P Q hP M

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (M : ModuleCategory (ZMod 2) D) :
    (kernelDerivedTensorOnBimoduleIdentityIso (ZMod 2) D).hom.app
        ((moduleToDerived (ZMod 2) D).obj M) =
      (kernelDerivedTensorAugmentation (ZMod 2) D D (Bimodule.diagonal (ZMod 2) D)).app M ≫
        (moduleToDerived (ZMod 2) D).map ((kernelIdentityClosedIso (ZMod 2) D).hom.app M) :=
  kernelDerivedTensorOnBimoduleIdentityIso_augmentation (ZMod 2) D M

#print axioms kernelResolutionTensorModelIso_hom_app
#print axioms kernelResolutionTensorModelIso_augmentation
#print axioms kernelDerivedTensorOnBimoduleCompositionIso_augmentation
#print axioms kernelDerivedTensorOnBimoduleCompositionIso_relativeKFlat
#print axioms kernelIdentityHomotopyIso_hom_app
#print axioms kernelIdentityHomotopyIso_computation
#print axioms kernelInputResolutionDerivedCounitIso_hom_app
#print axioms kernelDerivedTensorOnBimoduleIdentityIso_model
#print axioms kernelDerivedTensorOnBimoduleIdentityIso_augmentation
