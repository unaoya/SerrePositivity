module

public import SerrePositivity.KST.Descent.AugmentedCechSpaces
public import SerrePositivity.KST.Descent.DiagramTransfer
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# 実際の指定 Čech 降下の retract 安定性

## 概要
増強元と図式を同時に保つ retract から、実際の指定ホモトピー比較の retract を導く。

## 方針
指定比較の自然性に既存の矢の圏の retract 構成を適用し、弱同値の retract 安定性を使う。

## 規約
通常の極限への比較を使わず、指定された実際のホモトピー極限への比較を保持する。

## 使われ方
論文 補題 3.2 の transfer による降下の移行。原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DiagramModel

namespace SerrePositivity.KST.Descent

variable (K : Type u) [SmallCategory K] [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]

/-- 概要：増強図式の retract は指定ホモトピー比較の retract を与える（補題 3.2）。
方針：実際の指定比較の自然性を使う。
規約：始域の値と図式の全ての射の分裂を保持。使われ方：transfer による実降下の移行。 -/
def cechSpaceComparisonRetract {A B : AugmentedCechDiagram K} (h : Retract A B) :
    RetractArrow ((homotopyCechAugmentation K I J).app A)
      ((homotopyCechAugmentation K I J).app B) :=
  naturalComparisonRetract (cechAugmentedSource K)
    (cechAugmentedDiagram K ⋙ HomotopyCones.functor K I J)
    (homotopyCechAugmentation K I J) h

/-- 概要：実際の指定 Čech 降下は増強図式の retract へ移る（補題 3.2）。
方針：指定比較の矢の圏の retract と模型の弱同値の retract 安定性を使う。
規約：図式の fibrancy や追加の局所化入力は不要。使われ方：分裂側から元の比較へ戻す。 -/
theorem cechSpaceDescent_of_retract {A B : AugmentedCechDiagram K}
    (h : Retract A B) (hB : HasCechSpaceDescent K I J B) :
    HasCechSpaceDescent K I J A :=
  (weakEquivalences SSet.{u}).of_retract (cechSpaceComparisonRetract K I J h) hB

end SerrePositivity.KST.Descent
