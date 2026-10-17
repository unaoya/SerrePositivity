module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceIdentity
public import Mathlib.Data.ZMod.Basic

/-! # 対角kernelの恒等作用と入力解像度増大の監査

## 概要
主導来kernelの恒等作用を、局所Hom条件なしで検査する。

## 方針
任意の導来入力、任意の指定入力解像度族、標数2で型を確認し、公開7宣言を直接監査する。

## 規約と注意
入力解像度のCounitIsoは増大比較であり、一般kernelのtensor–Hom随伴の余単位とは別である。

## 使われ方
U16aのkernelIdentityIsoと、今後の合成比較の単位整合性の再現入口。
-/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.Morita

example (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D] :
    kernelDerivedTensor A D D (kernelIdentity A D) ≅ 𝟭 (DerivedModuleCategory A D) :=
  kernelIdentityIso A D

example (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleDerivedResolutionFunctor A D R ⋙ moduleHomotopyToDerivedClosed A D ≅
      𝟭 (DerivedModuleCategory A D) :=
  kernelInputResolutionDerivedCounitIso A D R

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (X : DerivedModuleCategory (ZMod 2) D) :
    (kernelDerivedTensor (ZMod 2) D D (kernelIdentity (ZMod 2) D)).obj X ≅ X :=
  (kernelIdentityIso (ZMod 2) D).app X

#print axioms kernelIdentityClosedIso
#print axioms kernelIdentityHomotopyIso
#print axioms kernelInputResolutionHomotopyAugmentation
#print axioms kernelInputResolutionDerivedAugmentationIso
#print axioms kernelInputResolutionDerivedCounitIso
#print axioms kernelDerivedTensorOnBimoduleIdentityIso
#print axioms kernelIdentityIso
