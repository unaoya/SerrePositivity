module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveProductEndpointTransport

/-!
# 中断した任意モデル源への一般化：NerveNaturalBoundaryTransport

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Transporting a fixed whole natural boundary through actual parameter squares。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0486][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0486
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Transporting a fixed whole natural boundary through actual parameter squares
-/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel
open NerveBiparameterMaps NerveCylinderBoundary NerveProductParameter

namespace SerrePositivity.SimplicialModel.NerveNaturalBoundaryTransport
variable {D : Type uD} [Category.{vD} D]
  (V K W L F : D ⥤ SSet.{w}) (i : V ⟶ K) (j : W ⟶ L) (f : K ⟶ L) (g : V ⟶ W)
  (hs : i ≫ f = g ≫ j) (a : NerveBiparameter.System L F) (b : W ⟶ F)
  (hb : a ≫ restriction W L F j = NerveNaturalBoundary.ofNatTrans W F b)

include hs hb in
lemma restrict_square : restrict K L F f a ≫ restriction V K F i =
    NerveNaturalBoundary.ofNatTrans V F (g ≫ b) := by
  change (a ≫ restriction K L F f) ≫ restriction V K F i = _
  rw [Category.assoc, restriction_comp, hs, ← restriction_comp, ← Category.assoc,
    hb, restrict_natural]

include hs in
lemma horizontal_square (T : SSet.{w}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V K i T ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal K L f T = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V W g T ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal W L j T := by
  apply NatTrans.ext
  funext d
  change i.app d ▷ T ≫ f.app d ▷ T = g.app d ▷ T ≫ j.app d ▷ T
  rw [← comp_whiskerRight, ← comp_whiskerRight]
  exact congrArg (fun k => k ▷ T) (congr_app hs d)

variable (T : SSet.{w}) (c : NerveBiparameter.System (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product L T) F)
  (d : W ⟶ F)
  (hc : c ≫ restriction _ _ F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal W L j T) =
    NerveNaturalBoundary.ofNatTrans _ _ (projection W T ≫ d))

include hs hc in
lemma horizontal_fixed : restrict _ _ F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal K L f T) c ≫
    restriction _ _ F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V K i T) =
    NerveNaturalBoundary.ofNatTrans _ _ (projection V T ≫ g ≫ d) := by
  apply (restrict_square (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product V T) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K T) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product W T) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product L T) F
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V K i T) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal W L j T) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal K L f T) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V W g T)
    (horizontal_square V K W L i j f g hs T) c (projection W T ≫ d) hc).trans
  apply congrArg (NerveNaturalBoundary.ofNatTrans _ _)
  rw [← Category.assoc, projection_horizontal, Category.assoc]

end SerrePositivity.SimplicialModel.NerveNaturalBoundaryTransport
