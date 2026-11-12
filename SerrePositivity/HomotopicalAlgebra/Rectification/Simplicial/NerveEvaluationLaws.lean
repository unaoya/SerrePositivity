module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBiparameterEvaluation
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveProductParameter

/-!
# 中断した任意モデル源への一般化：NerveEvaluationLaws

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual objectwise evaluation of whole restriction and natural-boundary equations。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0471][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0471
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual objectwise evaluation of whole restriction and natural-boundary equations
-/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.SimplicialModel.NerveEvaluationLaws
variable {D : Type uD} [Category.{vD} D] (K : D ⥤ SSet.{max w v}) (F : D ⥤ SSet.{v})

lemma restriction (L : D ⥤ SSet.{max w v}) (i : L ⟶ K)
    (a : NerveMovingParameter.System K F) (b : NerveMovingParameter.System L F)
    (h : a ≫ NerveBiparameterMaps.restriction L K (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted F) i = b)
    (d : D) : i.app d ≫ NerveMovingParameter.evaluate K F a d =
      NerveMovingParameter.evaluate L F b d :=
  (NerveBiparameterMaps.evaluate_restrict K F a L i d).symm.trans
    (congrArg (fun z => NerveMovingParameter.evaluate L F z d) h)

lemma natural (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} F) (d : D) :
    NerveMovingParameter.evaluate K F
      (NerveNaturalBoundary.ofNatTrans K (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted F) b) d = b.app d := by
  change uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫
    (NerveNaturalBoundary.ofNatTrans K (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted F) b).app
      (ofChain (ComposableArrows.mk₀ d))) = _
  rw [NerveNaturalBoundary.ofNatTrans_zero _ _ _ _ rfl]
  change uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫
    (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name (b.app d ≫ 𝟙 _))) = _
  rw [Category.comp_id, show SSet.stdSimplex.isTerminalObj₀.from
    (SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 0)) = 𝟙 _ from
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _, Category.id_comp,
    RelativeChoiceSpace.name, Iso.inv_hom_id_assoc, uncurry'_curry']

lemma expand (T : SSet.{max w v}) (a : NerveMovingParameter.System K F) (d : D) :
    NerveMovingParameter.evaluate (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K T) F
      (NerveProductParameter.expand K (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted F) T a) d =
    (NerveProductParameter.projection K T).app d ≫ NerveMovingParameter.evaluate K F a d :=
  NerveBiparameterMaps.evaluate_restrict K F a _ _ d

end SerrePositivity.SimplicialModel.NerveEvaluationLaws
