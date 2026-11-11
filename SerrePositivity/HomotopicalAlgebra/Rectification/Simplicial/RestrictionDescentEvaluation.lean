module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RestrictionDescentChoices

/-!
# 中断した任意モデル源への一般化：RestrictionDescentEvaluation

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The comparison family restricts to the original map over the whole parameter。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0546][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0546
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The comparison family restricts to the original map over the whole parameter
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.RestrictionDescentChoices

lemma constant_name_family {A K T : SSet.{v}} (h : A ⟶ K)
    (p : T ⟶ SSet.stdSimplex.obj (SimplexCategory.mk 0)) :
    uncurry (p ≫ RelativeChoiceSpace.name h) = fst A T ≫ h := by
  rw [RelativeChoiceSpace.name, ← Category.assoc, uncurry_natural_left]
  dsimp only [curry']
  rw [uncurry_curry]
  have hp : p ≫ RelativeChoiceSpace.pointUnitIso.hom = toUnit T :=
    CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
  rw [hp]
  rfl

variable {A B K : SSet.{v}} (a : A ⟶ B)
  (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
  (hK : SSet.modelCategoryQuillen.J.rlp (CategoryTheory.Limits.terminal.from K))

def fixedFamilyComparison {T : SSet.{v}} (h : A ⟶ K) (c : T ⟶ obj a h) :
    SSet.Homotopy (a ▷ T ≫ family a ha hK h c) (fst A T ≫ h) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints (familyComparison a ha hK h c) rfl
    (by rw [← Category.assoc]; exact constant_name_family h (c ≫ toPoint a h))

end SerrePositivity.SimplicialModel.RestrictionDescentChoices
