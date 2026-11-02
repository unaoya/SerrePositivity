module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceAssociator
public import Mathlib.Data.ZMod.Basic

/-! # 任意主導来kernelの作用結合図式の監査

## 概要
全kernel版の結合経路の等式を独立宇宙と標数2で検査する。

## 方針
公開kernelと公開左右経路そのものを使い、代表のK-flat性を仮定しない。

## 規約と注意
局所Hom条件はD・Eだけ。全体U16の受入は他の契約も検査して行う。

## 使われ方
U16aとPerf制限への作用結合coherenceの検証入口。
-/
@[expose] public section
noncomputable section
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
open SerrePositivity.DifferentialGraded.Morita
universe u v w z t
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (G : Type t) [DGCategory A G] [Small.{u} G]

example (hD : localHomKFlat A D) (hE : localHomKFlat A E)
    (P : Kernel A D E) (Q : Kernel A E F) (R : Kernel A F G) :
    kernelAssociatorLeftPath A D E F G hD P Q R =
      kernelAssociatorRightPath A D E F G hD hE P Q R :=
  kernelCompositionIso_associator A D E F G hD hE P Q R

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E]
    (F : Type z) [DGCategory (ZMod 2) F] [Small.{0} F]
    (G : Type t) [DGCategory (ZMod 2) G] [Small.{0} G]
    (hD : localHomKFlat (ZMod 2) D) (hE : localHomKFlat (ZMod 2) E)
    (P : Kernel (ZMod 2) D E) (Q : Kernel (ZMod 2) E F) (R : Kernel (ZMod 2) F G) :
    kernelAssociatorLeftPath (ZMod 2) D E F G hD P Q R =
      kernelAssociatorRightPath (ZMod 2) D E F G hD hE P Q R :=
  kernelCompositionIso_associator (ZMod 2) D E F G hD hE P Q R

#print axioms kernelAssociatorPaths_eq_of_first_iso
#print axioms kernelAssociatorPaths_eq_of_second_iso
#print axioms kernelCompositionIso_associator
