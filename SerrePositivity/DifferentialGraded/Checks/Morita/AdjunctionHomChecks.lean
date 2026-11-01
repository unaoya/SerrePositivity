module
public import SerrePositivity.DifferentialGraded.Morita.Perfect
public import Mathlib.Data.ZMod.Basic

/-! # 任意kernelの通常Hom dg関手の全Hom・閉零評価監査

## 概要
任意可換環・独立宇宙で通常Homを構成し、元の全Hom複体との一致を確認する。

## 方針
射の評価が全Hom endの後合成であることを検査し、全追加宣言を直接公理監査する。

## 規約と注意
kernelの射影性や全加群型のSmallを要求しない。導来右随伴の受入ではない。

## 使われ方
U16aの通常tensor–Hom随伴と導来右随伴の構成の再現入口。
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

example (P : Bimodule A E D) (N : RightModule A E) (d : D) :
    ((kernelHom A D E P).obj N).obj (Opposite.op d) = moduleHom A E (P.rightAt d) N :=
  kernelHom_value A D E P N d

example (P : Bimodule A E D) {M N : ModuleCategory A E} (f : M ⟶ N) (d : D) :
    (moduleEvaluation A D d).map ((kernelHom A D E P).onClosed.map f) =
      eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) (P.rightAt d)) f :=
  kernelHom_map_eval A D E P f d

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E] (P : Bimodule (ZMod 2) E D) :
    DGFunctor (ZMod 2) (RightModule (ZMod 2) E) (RightModule (ZMod 2) D) :=
  kernelHom (ZMod 2) D E P

#print axioms kernelHomModule
#print axioms kernelHomParam
#print axioms kernelHom
#print axioms kernelHom_value
#print axioms kernelHom_map_π
#print axioms kernelHom_map_eval
