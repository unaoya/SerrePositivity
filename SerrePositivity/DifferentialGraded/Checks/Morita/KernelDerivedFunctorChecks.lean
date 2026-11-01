module
public import SerrePositivity.DifferentialGraded.Morita.Kernel
public import Mathlib.Data.ZMod.Basic

/-! # 主導来kernelの作用・準同型反転・任意解像度計算の監査

## 概要
両変数の主導来圏上にあるkernel作用と、通常kernelの任意入力解像度による計算を確認する。

## 方針
独立宇宙・任意可換環・標数2で型を検査し、追加公開22宣言を直接監査する。

## 規約と注意
localHomKFlatは不要。一般右随伴と恒等／合成の作用coherenceの完成を意味しない。

## 使われ方
U16aの主導来kernel作用の再現入口。U16b/dは同じ作用関手と比較同型を使う。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.Morita
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

example : Kernel A D E ⥤ (DerivedModuleCategory A D ⥤ DerivedModuleCategory A E) :=
  kernelDerivedTensorFunctor A D E

example (P : Bimodule A E D) (M : ModuleCategory A D)
    (R : ModuleProjectiveResolution A D M) :
    (kernelDerivedTensor A D E
        ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).obj
        ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj R.obj) :=
  kernelDerivedTensorComputation A D E P M R

example (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    {P P' : BimoduleCategory A E D} (f : P ⟶ P')
    (hf : BimoduleCategory.quasiIso A E D f) :
    IsIso (kernelResolutionDerivedTensorMap A D E R f) :=
  kernelResolutionDerivedTensorMap_isIso A D E R f hf

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E]
    (P : Kernel (ZMod 2) D E) :
    DerivedModuleCategory (ZMod 2) D ⥤ DerivedModuleCategory (ZMod 2) E :=
  kernelDerivedTensor (ZMod 2) D E P

#check kernelDerivedTensorFunctor
#check kernelDerivedTensor
#check kernelDerivedTensorComputation
#check kernelDerivedTensorOnBimoduleIso
#print axioms kernelClosedFamilyNatTrans
#print axioms kernelTensorMap
#print axioms kernelTensorMap_app
#print axioms kernelTensorMap_id
#print axioms kernelTensorMap_comp
#print axioms kernelTensorHomotopyMap
#print axioms kernelTensorHomotopyMap_app
#print axioms kernelTensorHomotopyMap_id
#print axioms kernelTensorHomotopyMap_comp
#print axioms kernelTensorMap_value
#print axioms kernelTensorMap_projective_quasiIso
#print axioms kernelResolutionDerivedTensorMap
#print axioms kernelResolutionDerivedTensorMap_id
#print axioms kernelResolutionDerivedTensorMap_comp
#print axioms kernelResolutionDerivedTensorMap_isIso
#print axioms kernelDerivedTensorOnBimoduleFunctor
#print axioms kernelDerivedTensorOnBimoduleFunctor_inverts
#print axioms kernelDerivedTensorFunctor
#print axioms kernelDerivedTensorFunctor_fac
#print axioms kernelDerivedTensor
#print axioms kernelDerivedTensorOnBimoduleIso
#print axioms kernelDerivedTensorComputation
