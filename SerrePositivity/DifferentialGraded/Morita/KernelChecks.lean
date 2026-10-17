module
public import SerrePositivity.DifferentialGraded.Morita.KernelTensor

/-! # U16a kernelの公開型・通常作用の監査

## 概要
kernelの向き、主導来合成、graph作用との一致の公開契約を確認する。

## 方針
独立対象宇宙の型検査と公開8宣言の直接公理監査を行う。

## 規約と注意
一般右随伴など「型のみ確定」の予定宣言の存在を証明する検査ではない。

## 使われ方
formalization-plans/dg-theory-morita.mdの公開API契約を再現する入口。
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

example (hD : localHomKFlat A D) (P : Kernel A D E) (Q : Kernel A E F) : Kernel A D F :=
  kernelCompose A D E F hD P Q

example (f : DGFunctor A D E) :
    kernelTensor A D E (functorGraph A D E f) = dgModuleExtension A D E f :=
  kernelTensor_graph A D E f

#check Kernel
#check kernelIdentity
#check kernelGraph
#check kernelCompose
#check kernelComposeMap
#check kernelTensor
#check kernelTensor_value
#check kernelTensor_graph
#print axioms Kernel
#print axioms kernelIdentity
#print axioms kernelGraph
#print axioms kernelCompose
#print axioms kernelComposeMap
#print axioms kernelTensor
#print axioms kernelTensor_value
#print axioms kernelTensor_graph
