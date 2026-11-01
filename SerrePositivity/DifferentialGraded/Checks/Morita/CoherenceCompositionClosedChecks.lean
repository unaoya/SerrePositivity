module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKernel

public import Mathlib.Data.ZMod.Basic

/-! # 通常合成・相対K-flat入力計算と自然な解像度モデルの監査

## 概要
独立宇宙の任意可換環で通常／H⁰の合成と、任意解像度の関手計算を確認する。

## 方針
相対K-flat入力の計算を局所Hom条件なしで確認し、標数2の合成と追加全公開宣言の公理を検査する。

## 規約と注意
一般右随伴および全導来kernelの合成coherenceの受入ではない。

## 使われ方
U16aの合成比較の基盤を再現する独立入口。
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

example (P : Bimodule A E D) (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    (kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj M) :=
  kernelRelativeKFlatComputation A D E P M hM

example (P : Bimodule A E D)
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleToDerived A D ⋙ kernelResolutionDerivedTensor A D E P R ≅
      kernelResolutionTensorModelFunctor A D E P R :=
  kernelResolutionTensorModelIso A D E P R

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E]
    (F : Type z) [DGCategory (ZMod 2) F] [Small.{0} F]
    (P : Bimodule (ZMod 2) E D) (Q : Bimodule (ZMod 2) F E) :
    (kernelTensor (ZMod 2) D E P).onHomotopy ⋙ (kernelTensor (ZMod 2) E F Q).onHomotopy ≅
      (kernelTensor (ZMod 2) D F (BimoduleTensor.compose (ZMod 2) F E D Q P)).onHomotopy :=
  kernelTensorCompositionHomotopyIso (ZMod 2) D E F P Q

#print axioms kernelTensor_map_π
#print axioms kernelTensor_map_eval
#print axioms kernelTensor_relativeKFlat_quasiIso
#print axioms kernelTensorHomotopyComputation_naturality
#print axioms kernelTensorHomotopyComputationIso
#print axioms kernelResolutionTensorAugmentation
#print axioms kernelResolutionTensorAugmentation_app
#print axioms kernelDerivedTensorAugmentation
#print axioms kernelDerivedTensorAugmentation_app
#print axioms kernelDerivedTensorAugmentation_isIso_of_relativeKFlat
#print axioms kernelRelativeKFlatComputation
#print axioms kernelTensorComposition_map
#print axioms kernelTensorComposition_eq
#print axioms kernelTensorCompositionSourceIso
#print axioms kernelTensorAssociatorClosedIso
#print axioms kernelTensorCompositionClosedIso
#print axioms kernelTensorCompositionHomotopyIso
#print axioms kernelResolutionTensorModelFunctor
#print axioms kernelResolutionTensorModelIso
#print axioms kernelResolutionTensorModelFunctor_map
#print axioms kernelTensor_relativeKFlat
