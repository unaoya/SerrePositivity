module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBiparameterComposition

/-!
# 中断した任意モデル源への一般化：NerveProductEndpointTransport

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Whole endpoint equations survive the actual parameter and value transports。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0489][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0489
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Whole endpoint equations survive the actual parameter and value transports
-/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.NerveProductEndpointTransport
open NerveBiparameterMaps NerveCylinderBoundary NerveProductParameter
variable {D : Type uD} [Category.{vD} D] (V K F G : D ⥤ SSet.{w})
  (i : V ⟶ K) (p : F ⟶ G)

lemma mapTarget_restrict (a : NerveBiparameter.System K F) :
    mapTarget K F G p a ≫ restriction V K G i = mapTarget V F G p (a ≫ restriction V K F i) := by
  change (a ≫ targetMap _ _ _ _) ≫ _ = (a ≫ _) ≫ _
  rw [Category.assoc, target_restriction, ← Category.assoc]

variable {A T : SSet.{w}} (j : A ⟶ T) (a : NerveBiparameter.System (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K T) F)
  (b : NerveBiparameter.System K F)
  (he : a ≫ restriction (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K A) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K T) F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical j K) = expand K F A b)

include he in
lemma mapTarget_endpoint : mapTarget (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K T) F G p a ≫
    restriction (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K A) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K T) G (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical j K) =
      expand K G A (mapTarget K F G p b) := by
  rw [mapTarget_restrict, he, ← expand_mapTarget]

include he in
lemma restrict_endpoint : restrict (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product V T) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K T) F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V K i T) a ≫
    restriction (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product V A) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product V T) F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical j V) =
      expand V F A (restrict V K F i b) := by
  change (a ≫ restriction _ _ _ _) ≫ _ = _
  rw [Category.assoc, restriction_comp, ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.commute V K i j, ← restriction_comp,
    ← Category.assoc, he]
  exact expand_horizontal K F A V i b

end SerrePositivity.SimplicialModel.NerveProductEndpointTransport
