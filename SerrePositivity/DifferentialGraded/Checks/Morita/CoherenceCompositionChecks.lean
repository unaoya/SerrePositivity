module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceComposition
public import SerrePositivity.DifferentialGraded.Morita.PerfectDerivedKernelCoherence
public import Mathlib.Data.ZMod.Basic

/-! # 主導来kernelの合成作用と既存Perfアダプタの接続検査

## 概要
任意の主導来kernelについて、必要な始域Hom条件だけで合成比較が使えることを確認する。

## 方針
独立宇宙・標数2と、U16dの実際のPerf保存への適用を同じ公開入口で検査する。

## 規約と注意
kernel射の自然性・単位と結合のcoherence、一般右随伴の完成を意味しない。

## 使われ方
U16aの合成比較とU16dへの引継ぎのビルド・主要公理監査を再現する。
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

example (hD : localHomKFlat A D) (P : Kernel A D E) (Q : Kernel A E F) :
    kernelDerivedTensor A D E P ⋙ kernelDerivedTensor A E F Q ≅
      kernelDerivedTensor A D F (kernelCompose A D E F hD P Q) :=
  kernelCompositionIso A D E F hD P Q

example (hD : localHomKFlat A D) (P : Kernel A D E) (Q : Kernel A E F)
    (hP : kernelColumnsPerfect A D E P) (hQ : kernelColumnsPerfect A E F Q) :
    kernelColumnsPerfect A D F (kernelCompose A D E F hD P Q) :=
  kernelCompose_columnsPerfect A D E F hD P Q hP hQ
    (kernelCompositionIso A D E F hD P Q)

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E]
    (F : Type z) [DGCategory (ZMod 2) F] [Small.{0} F]
    (hD : localHomKFlat (ZMod 2) D) (P : Kernel (ZMod 2) D E) (Q : Kernel (ZMod 2) E F) :
    kernelDerivedTensor (ZMod 2) D E P ⋙ kernelDerivedTensor (ZMod 2) E F Q ≅
      kernelDerivedTensor (ZMod 2) D F (kernelCompose (ZMod 2) D E F hD P Q) :=
  kernelCompositionIso (ZMod 2) D E F hD P Q

#check kernelCompositionIso
#print axioms kernelResolutionTensorCompositionIso
#print axioms kernelDerivedTensorOnBimoduleCompositionIso
#print axioms kernelCompositionKFlatIso
#print axioms kernelCompositionIso
