module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelGeneratorHom
public import Mathlib.Data.ZMod.Basic

/-! # 任意kernelのtelescopeと生成元Hom比較の監査

## 概要
独立対象宇宙・任意可換環でtelescopeの存在と全生成元上のHom全単射を検査する。

## 方針
実際に選んだtelescopeにも一般定理を適用し、標数2のkernelを含めて型と公理を確認する。

## 規約と注意
全入力のHom表現と一般右随伴は未完。この入口はU16a全受入を意味しない。

## 使われ方
U16aの右随伴の表現対象を構成する中間単位の再現入口。
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

example (K : Kernel A D E) (Y : DerivedModuleCategory A E) :
    Nonempty (KernelBrownTelescope A D E K Y) := kernelBrownTelescope_nonempty A D E K Y

example (K : Kernel A D E) (Y : DerivedModuleCategory A E) (p : D × ℤ) :
    Function.Bijective (fun f : moduleCompactGenerators A D p ⟶
      (kernelBrownTelescope A D E K Y).obj =>
        (kernelDerivedTensor A D E K).map f ≫ (kernelBrownTelescope A D E K Y).target) :=
  kernelBrownTelescope_generator_bijective A D E K Y (kernelBrownTelescope A D E K Y) p

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E]
    (K : Kernel (ZMod 2) D E) (Y : DerivedModuleCategory (ZMod 2) E) (p : D × ℤ) :
    Function.Bijective (fun f : moduleCompactGenerators (ZMod 2) D p ⟶
      (kernelBrownTelescope (ZMod 2) D E K Y).obj =>
        (kernelDerivedTensor (ZMod 2) D E K).map f ≫
          (kernelBrownTelescope (ZMod 2) D E K Y).target) :=
  kernelBrownTelescope_generator_bijective (ZMod 2) D E K Y
    (kernelBrownTelescope (ZMod 2) D E K Y) p

#print axioms kernelBrownObjects
#print axioms kernelBrownSumTarget
#print axioms kernelBrownSumTarget_ι
#print axioms kernelBrownActionAdditive
#print axioms kernelBrownSumTarget_relation
#print axioms KernelBrownTelescope
#print axioms kernelBrownTelescope_nonempty
#print axioms kernelBrownTelescope
#print axioms kernelBrownStageMap
#print axioms kernelBrownStageMap_fac
#print axioms kernelBrownStageMap_succ
#print axioms kernelBrownTelescope_generator_surjective
#print axioms kernelBrownTelescope_generator_kernel_zero
#print axioms kernelBrownTelescope_generator_bijective
