module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorPaths
public import Mathlib.Data.ZMod.Basic

/-! # 公開作用の結合二経路のK-flatモデル上での一致の監査

## 概要
公開された主導来作用・合成比較・kernel結合子による二経路の等式を指定モデルで検査する。

## 方針
独立対象宇宙・任意可換環で実際の二経路を使い、最後のkernelを任意のままに保つ。

## 規約と注意
任意の主導来kernelへの選択変更は後続の課題。U16a全受入とは区別する。

## 使われ方
U16aの結合coherenceの二経路の貼合せを再現する入口。
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

example (hD : localHomKFlat A D) (hE : localHomKFlat A E)
    (P : RightKFlatBimoduleCategory A E D) (Q : RightKFlatBimoduleCategory A F E)
    (R : BimoduleCategory A G F) :
    kernelAssociatorLeftPath A D E F G hD ((bimoduleToDerived A E D).obj P.obj)
        ((bimoduleToDerived A F E).obj Q.obj) ((bimoduleToDerived A G F).obj R) =
      kernelAssociatorRightPath A D E F G hD hE ((bimoduleToDerived A E D).obj P.obj)
        ((bimoduleToDerived A F E).obj Q.obj) ((bimoduleToDerived A G F).obj R) :=
  kernelCompositionIso_associator_model A D E F G hD hE P Q R

example (hD : localHomKFlat A D) (hE : localHomKFlat A E)
    (P : Kernel A D E) (Q : Kernel A E F) (R : Kernel A F G) :
    (kernelDerivedTensor A D E P ⋙ kernelDerivedTensor A E F Q) ⋙ kernelDerivedTensor A F G R ⟶
      kernelDerivedTensor A D G
        (kernelCompose A D F G hD (kernelCompose A D E F hD P Q) R) :=
  kernelAssociatorRightPath A D E F G hD hE P Q R

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E]
    (F : Type z) [DGCategory (ZMod 2) F] [Small.{0} F]
    (G : Type t) [DGCategory (ZMod 2) G] [Small.{0} G]
    (hD : localHomKFlat (ZMod 2) D) (hE : localHomKFlat (ZMod 2) E)
    (P : RightKFlatBimoduleCategory (ZMod 2) E D)
    (Q : RightKFlatBimoduleCategory (ZMod 2) F E) (R : BimoduleCategory (ZMod 2) G F) :
    kernelAssociatorLeftPath (ZMod 2) D E F G hD
        ((bimoduleToDerived (ZMod 2) E D).obj P.obj)
        ((bimoduleToDerived (ZMod 2) F E).obj Q.obj) ((bimoduleToDerived (ZMod 2) G F).obj R) =
      kernelAssociatorRightPath (ZMod 2) D E F G hD hE
        ((bimoduleToDerived (ZMod 2) E D).obj P.obj)
        ((bimoduleToDerived (ZMod 2) F E).obj Q.obj) ((bimoduleToDerived (ZMod 2) G F).obj R) :=
  kernelCompositionIso_associator_model (ZMod 2) D E F G hD hE P Q R

#print axioms kernelCompositionIso_first_naturality
#print axioms kernelCompositionIso_second_naturality
#print axioms kernelAssociatorLeftPath
#print axioms kernelAssociatorRightPath
#print axioms kernelAssociatorLeftPath_model_fac
#print axioms kernelAssociatorPairPath_model_fac
#print axioms kernelAssociatorRightPath_model_fac
#print axioms kernelCompositionIso_associator_model
