module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.FrameLiftSpace

/-!
# 中断した任意モデル源への一般化：FrameSquareComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Comparing the two actual framed paths of an inner commuting square。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0086][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0086
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Comparing the two actual framed paths of an inner commuting square

Equality is required only for the underlying resolution maps. The original
outer-frame composites supply points in one fixed derived comparison space.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.FrameSquareComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {A B D E : FramedResolution C} (s : A ⟶ B) (t : B ⟶ E) (u : A ⟶ D) (v : D ⟶ E)
  (h : (s ≫ t).map = (u ≫ v).map)
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

abbrev obj : SSet.{v} := FrameLiftSpace.obj (s ≫ t).map
abbrev leftFrame : ResolutionLiftPrecomposition.FrameMap (s ≫ t).map :=
  FramedResolution.frameMap (s ≫ t)
abbrev rightFrame : ResolutionLiftPrecomposition.FrameMap (s ≫ t).map :=
  FrameLiftSpace.changeMap (s ≫ t).map h (FramedResolution.frameMap (u ≫ v))
abbrev leftPoint : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ obj s t :=
  FrameLiftSpace.point _ (leftFrame s t)
abbrev rightPoint : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ obj s t :=
  FrameLiftSpace.point _ (rightFrame s t u v h)

lemma leftFrame_val : (leftFrame s t).val = s.frame ≫ t.frame := rfl
lemma rightFrame_val : (rightFrame s t u v h).val = u.frame ≫ v.frame :=
  FrameLiftSpace.changeMap_val _ h _

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma interval : ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ obj s t,
    SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ e = leftPoint s t ∧
    SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ e = rightPoint s t u v h :=
  FrameLiftSpace.interval _ hcof (leftFrame s t) (rightFrame s t u v h)

include hcof in
lemma extension {K L : SSet.{v}} (i : K ⟶ L) [Mono i] (boundary : K ⟶ obj s t) :
    ∃ e : L ⟶ obj s t, i ≫ e = boundary := FrameLiftSpace.extension _ hcof i boundary

end SerrePositivity.HomotopyFunctionComplex.FrameSquareComparison
