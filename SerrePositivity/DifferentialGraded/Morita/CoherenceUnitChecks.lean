module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceUnitMain
public import Mathlib.Data.ZMod.Basic

/-! # 主導来kernel作用の右単位coherenceの監査

## 概要
通常kernelから主局所化の任意kernelまで、恒等を先に作用させる右単位図式を検査する。

## 方針
独立対象宇宙・任意可換環と標数2で、既存の主導来右単位子と公開作用比較を同時に用いる。

## 規約と注意
始域Dの局所Hom K-flat性だけを保持。左単位・結合coherenceの受入とは区別する。

## 使われ方
U16aの右単位図式とU16dのPerfへの制限の再現入口。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
open SerrePositivity.DifferentialGraded.Morita
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

example (hD : localHomKFlat A D) (P : Kernel A D E) :
    (kernelCompositionIso A D D E hD (kernelIdentity A D) P).hom ≫
      (kernelDerivedTensorFunctor A D E).map ((derivedBimoduleRightUnitIso A E D hD).hom.app P) =
    Functor.whiskerRight (kernelIdentityIso A D).hom (kernelDerivedTensor A D E P) ≫
      (Functor.leftUnitor (kernelDerivedTensor A D E P)).hom :=
  kernelCompositionIso_rightUnit A D E hD P

example (P : Bimodule A E D) :
    (kernelDerivedTensorOnBimoduleCompositionIso A D D E (Bimodule.diagonal A D) P
        (Bimodule.diagonal_rightRelativeKFlat A D)).hom ≫
      kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D)
        (rightBimoduleUnitIso A E D P).hom =
    Functor.whiskerRight (kernelDerivedTensorOnBimoduleIdentityIso A D).hom
        (kernelDerivedTensorOnBimodule A D E P) ≫
      (Functor.leftUnitor (kernelDerivedTensorOnBimodule A D E P)).hom :=
  kernelDerivedTensorOnBimoduleCompositionIso_rightUnit A D E P

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E]
    (hD : localHomKFlat (ZMod 2) D) (P : Kernel (ZMod 2) D E) :
    (kernelCompositionIso (ZMod 2) D D E hD (kernelIdentity (ZMod 2) D) P).hom ≫
      (kernelDerivedTensorFunctor (ZMod 2) D E).map
        ((derivedBimoduleRightUnitIso (ZMod 2) E D hD).hom.app P) =
    Functor.whiskerRight (kernelIdentityIso (ZMod 2) D).hom (kernelDerivedTensor (ZMod 2) D E P) ≫
      (Functor.leftUnitor (kernelDerivedTensor (ZMod 2) D E P)).hom :=
  kernelCompositionIso_rightUnit (ZMod 2) D E hD P

#print axioms kernelTensorFamilyMap
#print axioms kernelTensorCompositionClosedIso_rightUnit
#print axioms kernelActionNatTrans_ext_projective
#print axioms kernelDerivedTensorOnBimoduleCompositionIso_rightUnit_app
#print axioms kernelDerivedTensorOnBimoduleCompositionIso_rightUnit
#print axioms kernelCompositionTargetIso_rightUnit
#print axioms kernelCompositionIso_rightUnit
