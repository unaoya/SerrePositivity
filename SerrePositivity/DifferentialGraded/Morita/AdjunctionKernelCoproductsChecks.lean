module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelCoproducts
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionBrownSeed
public import Mathlib.Data.ZMod.Basic

/-! # 実際の主導来kernel作用の余積保存の監査

## 概要
任意の主導来kernelについて、u-small余積保存と初期被覆への実際の適用を検査する。

## 方針
独立宇宙・任意可換環・標数2で型を確認し、通常余極限・導来余積の全追加宣言を監査する。

## 規約と注意
局所Hom K-flat性やkernelの列の射影性を要求しない。

## 使われ方
U16aの一般右随伴構成へ、実際の余積保存を供給する再現入口。
-/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.Morita
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

example (K : Kernel A D E) (J : Type z) [Small.{u} J] :
    PreservesColimitsOfShape (Discrete J) (kernelDerivedTensor A D E K) :=
  kernelDerivedTensorPreservesCoproducts A D E K

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E] (K : Kernel (ZMod 2) D E)
    (J : Type z) [Small.{0} J] :
    PreservesColimitsOfShape (Discrete J) (kernelDerivedTensor (ZMod 2) D E K) :=
  kernelDerivedTensorPreservesCoproducts (ZMod 2) D E K

#print axioms kernelTensorIsColimit
#print axioms kernelTensorPreservesColimitsOfShape
#print axioms kernelDerivedTensorProjectiveCofanIsColimit
#print axioms kernelDerivedTensorPreservesProjectiveCoproduct
#print axioms kernelDerivedTensorOnBimodulePreservesCoproduct
#print axioms kernelDerivedTensorOnBimodulePreservesCoproducts
#print axioms kernelDerivedTensorPreservesCoproducts
