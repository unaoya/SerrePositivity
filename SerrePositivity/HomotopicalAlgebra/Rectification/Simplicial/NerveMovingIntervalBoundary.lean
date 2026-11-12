module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBinaryBoundary
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveProductParameter

/-!
# 中断した任意モデル源への一般化：NerveMovingIntervalBoundary

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual interval boundaries for changing tuple parameters, with a shared whole vertex system。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0482][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0482
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual interval boundaries for changing tuple parameters, with a shared whole vertex system
-/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.NerveMovingIntervalBoundary
open NerveCylinderBoundary NerveBiparameterMaps NerveProductParameter
abbrev point := BoundaryOneCotensor.vertex.{w}
abbrev ends := BoundaryOneCotensor.boundary.{w}
abbrev zero : point.{w} ⟶ ends.{w} := BoundaryOneCotensor.zero
abbrev one : point.{w} ⟶ ends.{w} := BoundaryOneCotensor.one

variable {D : Type uD} [Category.{vD} D] (K F : D ⥤ SSet.{w})

def coproduct (d : D) : IsColimit (BinaryCofan.mk
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical zero K).app d) ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical one K).app d)) :=
  mapIsColimitOfPreservesOfIsColimit (tensorLeft (K.obj d)) _ _
    HomotopyFunctionComplex.BoundaryOne.isColimit

/-- The actual K(start) × ∂Δ1 parameter keeps both independently given whole endpoint systems. -/
def glue (a b : NerveBiparameter.System K F) : NerveBiparameter.System (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K ends) F :=
  NerveBinaryBoundary.glue (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K point) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K point) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K ends) F
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical zero K) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical one K) (coproduct K)
    (expand K F point a) (expand K F point b)

lemma glue_zero (a b : NerveBiparameter.System K F) : glue K F a b ≫
    restriction (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K point) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K ends) F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical zero K) = expand K F point a :=
  NerveBinaryBoundary.glue_left _ _ _ _ _ _ _ _ _

lemma glue_one (a b : NerveBiparameter.System K F) : glue K F a b ≫
    restriction (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K point) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K ends) F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical one K) = expand K F point b :=
  NerveBinaryBoundary.glue_right _ _ _ _ _ _ _ _ _

lemma hom_ext {f g : NerveBiparameter.System (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K ends) F}
    (h₀ : f ≫ restriction (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K point) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K ends) F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical zero K) =
      g ≫ restriction (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K point) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K ends) F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical zero K))
    (h₁ : f ≫ restriction (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K point) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K ends) F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical one K) =
      g ≫ restriction (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K point) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K ends) F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical one K)) : f = g :=
  NerveBinaryBoundary.hom_ext _ _ _ _ _ _ (coproduct K) h₀ h₁

lemma glue_diagonal (a : NerveBiparameter.System K F) : glue K F a a = expand K F ends a := by
  apply hom_ext K F
  · rw [glue_zero, expand_vertical]
  · rw [glue_one, expand_vertical]

lemma glue_horizontal (V : D ⥤ SSet.{w}) (i : V ⟶ K) (a b : NerveBiparameter.System K F) :
    glue K F a b ≫ restriction (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product V ends) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K ends) F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V K i ends) =
      glue V F (a ≫ restriction V K F i) (b ≫ restriction V K F i) := by
  apply hom_ext V F
  · rw [Category.assoc, restriction_comp, ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.commute V K i zero,
      ← restriction_comp, ← Category.assoc, glue_zero, expand_horizontal, glue_zero]
  · rw [Category.assoc, restriction_comp, ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.commute V K i one,
      ← restriction_comp, ← Category.assoc, glue_one, expand_horizontal, glue_one]

variable (V : D ⥤ SSet.{w}) (i : V ⟶ K) (c : V ⟶ F)
  (a b : NerveBiparameter.System K F)
  (ha : a ≫ restriction V K F i = NerveNaturalBoundary.ofNatTrans V F c)
  (hb : b ≫ restriction V K F i = NerveNaturalBoundary.ofNatTrans V F c)
  {T : SSet.{w}} (j : ends.{w} ⟶ T)

include ha hb in
/-- Shared vertex compatibility is derived from the existing endpoint boundary equations. -/
lemma common_boundary : glue K F a b ≫
    restriction (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product V ends) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K ends) F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V K i ends) =
    NerveNaturalBoundary.ofNatTrans (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product V T) F (projection V T ≫ c) ≫
      restriction (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product V ends) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product V T) F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical j V) := by
  rw [glue_horizontal, ha, hb, glue_diagonal, ← expand_natural, expand_vertical]

end SerrePositivity.SimplicialModel.NerveMovingIntervalBoundary
