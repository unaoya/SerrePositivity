module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal

/-!
# 中断した任意モデル源への一般化：OrdinaryBarWordDiagonalEquivalence

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual diagonal word comparison is inverted without a large SSet model structure。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0241][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0241
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual diagonal word comparison is inverted without a large SSet model structure
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence
open OrdinaryBarFreeResolutionSeed
variable (C : Type u) [Category.{v} C] (X Y : D C)

lemma diagonal_augmentation_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarWordRows.diagonalAugmentation C X Y)) :=
  BisimplicialModel.localized_diagonal_map (OrdinaryBarWordRows.augmentation C X Y)
    (OrdinaryBarWordRows.localized_augmentation_app C X Y)

lemma toSource_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarWordRowsDiagonal.toSource C X Y)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (OrdinaryBarWordRows.diagonalAugmentation C X Y)) := diagonal_augmentation_isIso C X Y
  rw [OrdinaryBarWordRowsDiagonal.toSource, OrdinaryBarWordRows.toSource,
    Functor.map_comp, Functor.map_comp]
  infer_instance

lemma augmentation_isIso_iff_source :
    IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarAmbientWordComparison.augmentation C X Y)) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarSourceHom.augmentation C X Y)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (OrdinaryBarWordRowsDiagonal.toSource C X Y)) := toSource_isIso C X Y
  rw [OrdinaryBarWordRowsDiagonal.augmentation_factorization, Functor.map_comp]
  exact isIso_comp_left_iff _ _

lemma small_augmentation_isIso_iff_source :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y)) ↔
        IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarSourceHom.augmentation C X Y)) :=
  (OrdinaryBarAmbientWordComparison.localized_small_iff_words C X Y).trans
    (augmentation_isIso_iff_source C X Y)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence
