module
public import SerrePositivity.DifferentialGraded.Morita.KernelResolution
public import Mathlib.Data.ZMod.Basic

/-! # 任意通常kernelの解像度計算とgraph一致の監査

## 概要
局所Hom条件なしの主導来作用、任意入力解像度の計算と選択比較を確認する。

## 方針
任意可換環・独立対象宇宙の計算同型、標数2のgraph一致を検査し、公開10宣言を直接監査する。

## 規約と注意
kernel自体の局所化への降下と一般右随伴の完成を意味しない。

## 使われ方
U16aの入力解像度計算の再現入口。U16bはgraph一致を読み取り専用で再利用できる。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.Morita

example (A : Type u) [CommRing A]
    (D : Type v) [DGCategory A D] [Small.{u} D]
    (E : Type w) [DGCategory A E] [Small.{u} E]
    (P : Bimodule A E D) {M : ModuleCategory A D} (R : ModuleProjectiveResolution A D M) :
    (kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj R.obj) :=
  kernelDerivedTensorOnBimoduleComputation A D E P R

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E]
    (F : DGFunctor (ZMod 2) D E) :
    kernelDerivedTensorOnBimodule (ZMod 2) D E (functorGraph (ZMod 2) D E F) =
      dgDerivedExtension (ZMod 2) D E F :=
  kernelDerivedTensorOnBimodule_graph (ZMod 2) D E F

#print axioms kernelHomotopyToDerived
#print axioms kernelResolutionDerivedTensor
#print axioms kernelDerivedTensorOnBimodule
#print axioms kernelTensorHomotopyComputation
#print axioms kernelResolutionDerivedTensorComputation
#print axioms kernelResolutionDerivedTensorIso
#print axioms kernelResolutionDerivedTensorIso_self
#print axioms kernelResolutionDerivedTensorIso_trans
#print axioms kernelDerivedTensorOnBimoduleComputation
#print axioms kernelDerivedTensorOnBimodule_graph
