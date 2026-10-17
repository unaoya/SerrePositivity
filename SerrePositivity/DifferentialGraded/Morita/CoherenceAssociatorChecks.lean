module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorKFlat
public import Mathlib.Data.ZMod.Basic

/-! # 通常kernelと右K-flatモデルの結合coherenceの監査

## 概要
三つのkernelの通常作用・導来作用の結合図式を、独立対象宇宙で検査する。

## 方針
後のkernelにK-flat性を追加せず、全導来入力の自然変換の等式を利用して公理を出力する。

## 規約と注意
主導来kernel全体へのモデル変更は後続の検証対象。U16a全体の受入とは区別する。

## 使われ方
U16aの結合coherenceの同じ計算モデルの再現入口。
-/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
open SerrePositivity.DifferentialGraded.Morita
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (G : Type t) [DGCategory A G] [Small.{u} G]

example (P : Bimodule A E D) (Q : Bimodule A F E) (R : Bimodule A G F)
    (hP : Bimodule.rightRelativeKFlat A E D P) (hQ : Bimodule.rightRelativeKFlat A F E Q) :
    Functor.whiskerRight (kernelDerivedTensorOnBimoduleCompositionIso A D E F P Q hP).hom
        (kernelDerivedTensorOnBimodule A F G R) ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D F G
        (BimoduleTensor.compose A F E D Q P) R
        (Bimodule.rightRelativeKFlat_compose A F E D Q P hQ hP)).hom =
    (Functor.associator (kernelDerivedTensorOnBimodule A D E P)
      (kernelDerivedTensorOnBimodule A E F Q) (kernelDerivedTensorOnBimodule A F G R)).hom ≫
      Functor.whiskerLeft (kernelDerivedTensorOnBimodule A D E P)
        (kernelDerivedTensorOnBimoduleCompositionIso A E F G Q R hQ).hom ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D E G P
        (BimoduleTensor.compose A G F E R Q) hP).hom ≫
      kernelResolutionDerivedTensorMap A D G (moduleCanonicalProjectiveResolution A D)
        (associatorIso A G F E D R Q P).hom :=
  kernelDerivedTensorOnBimoduleCompositionIso_associator A D E F G P Q R hP hQ

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E]
    (F : Type z) [DGCategory (ZMod 2) F] [Small.{0} F]
    (G : Type t) [DGCategory (ZMod 2) G] [Small.{0} G]
    (P : Bimodule (ZMod 2) E D) (Q : Bimodule (ZMod 2) F E)
    (R : Bimodule (ZMod 2) G F) (M : ModuleCategory (ZMod 2) D) :
    (kernelTensor (ZMod 2) F G R).onClosed.map
        ((kernelTensorCompositionClosedIso (ZMod 2) D E F P Q).hom.app M) ≫
      (kernelTensorCompositionClosedIso (ZMod 2) D F G
        (BimoduleTensor.compose (ZMod 2) F E D Q P) R).hom.app M =
    (kernelTensorCompositionClosedIso (ZMod 2) E F G Q R).hom.app
        ((kernelTensor (ZMod 2) D E P).onClosed.obj M) ≫
      (kernelTensorCompositionClosedIso (ZMod 2) D E G P
        (BimoduleTensor.compose (ZMod 2) G F E R Q)).hom.app M ≫
      (kernelTensorMap (ZMod 2) D G (associatorIso (ZMod 2) G F E D R Q P).hom).app M :=
  kernelTensorCompositionClosedIso_associator (ZMod 2) D E F G P Q R M

#print axioms kernelTensorAssociatorFamily
#print axioms kernelTensorAssociator_inversePentagon
#print axioms kernelTensorCompositionClosedIso_associator
#print axioms kernelTripleAugmentation
#print axioms kernelAssociatorLeft_augmentation
#print axioms kernelAssociatorRight_augmentation
#print axioms kernelDerivedTensorOnBimoduleCompositionIso_associator_app
#print axioms kernelDerivedTensorOnBimoduleCompositionIso_associator
