module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveCylinderBoundary
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBiparameterMapLaws

/-!
# 中断した任意モデル源への一般化：NerveProductParameter

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Supplementary constant parameters in whole moving coherent systems。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0490][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0490
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Supplementary constant parameters in whole moving coherent systems
-/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.NerveProductParameter
open NerveCylinderBoundary NerveBiparameterMaps
variable {D : Type uD} [Category.{vD} D] (K F : D ⥤ SSet.{w}) (T : SSet.{w})

def projection : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K T ⟶ K where
  app d := fst (K.obj d) T
  naturality {_ _} f := whiskerRight_fst (K.map f) T

lemma projection_horizontal (V : D ⥤ SSet.{w}) (i : V ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V K i T ≫ projection K T = projection V T ≫ i := by
  apply NatTrans.ext
  funext d
  exact whiskerRight_fst (i.app d) T

lemma projection_vertical {A : SSet.{w}} (j : A ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical j K ≫ projection K T = projection K A := by
  apply NatTrans.ext
  funext d
  exact whiskerLeft_fst (K.obj d) j

/-- Retain the whole original system, constant in the supplementary parameter. -/
def expand (a : NerveBiparameter.System K F) : NerveBiparameter.System (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K T) F :=
  restrict (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K T) K F (projection K T) a

lemma expand_vertical {A : SSet.{w}} (j : A ⟶ T) (a : NerveBiparameter.System K F) :
    expand K F T a ≫ restriction (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K A) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K T) F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical j K) =
      expand K F A a := by
  change (a ≫ restriction _ _ _ _) ≫ _ = _
  rw [Category.assoc, restriction_comp, projection_vertical]
  rfl

lemma expand_horizontal (V : D ⥤ SSet.{w}) (i : V ⟶ K)
    (a : NerveBiparameter.System K F) : expand K F T a ≫
    restriction (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product V T) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K T) F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V K i T) =
      expand V F T (a ≫ restriction V K F i) := by
  change (a ≫ restriction _ _ _ _) ≫ _ = (a ≫ _) ≫ _
  rw [Category.assoc, restriction_comp, projection_horizontal,
    Category.assoc, restriction_comp]

lemma expand_natural (b : K ⟶ F) : expand K F T (NerveNaturalBoundary.ofNatTrans K F b) =
    NerveNaturalBoundary.ofNatTrans (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K T) F (projection K T ≫ b) :=
  restrict_natural _ _ _ _ _

end SerrePositivity.SimplicialModel.NerveProductParameter
