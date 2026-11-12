module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBiparameterMapLaws

/-!
# 中断した任意モデル源への一般化：NerveBiparameterEvaluation

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Recovering actual whole maps after parameter and value transport。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0461][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0461
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Recovering actual whole maps after parameter and value transport
-/

@[expose] public section
universe w v uD vD uE vE
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.SimplicialModel.NerveBiparameterMaps
variable {D : Type uD} [Category.{vD} D]
  (K : D ⥤ SSet.{max w v}) (F : D ⥤ SSet.{v}) (a : NerveMovingParameter.System K F)

lemma name_evaluate (d : D) : RelativeChoiceSpace.name (NerveMovingParameter.evaluate K F a d) =
    a.app (ofChain (ComposableArrows.mk₀ d)) := by
  change RelativeChoiceSpace.pointUnitIso.hom ≫
    curry' (uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫
      a.app (ofChain (ComposableArrows.mk₀ d)))) = _
  rw [curry'_uncurry', Iso.hom_inv_id_assoc]

lemma evaluate_mapTarget (G : D ⥤ SSet.{v}) (p : F ⟶ G) (d : D) :
    NerveMovingParameter.evaluate K G
      (mapTarget K (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted F) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted G)
        (Functor.whiskerRight p SSet.uliftFunctor.{w, v}) a) d =
      NerveMovingParameter.evaluate K F a d ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} (p.app d) := by
  change uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫
    (a.app (ofChain (ComposableArrows.mk₀ d)) ≫
      (ihom (K.obj d)).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} (p.app d)))) = _
  rw [← name_evaluate K F a d, RelativeChoiceSpace.name_postcomp,
    RelativeChoiceSpace.name, Iso.inv_hom_id_assoc, uncurry'_curry']

lemma evaluate_restrict (L : D ⥤ SSet.{max w v}) (i : L ⟶ K) (d : D) :
    NerveMovingParameter.evaluate L F (restrict L K (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted F) i a) d =
      i.app d ≫ NerveMovingParameter.evaluate K F a d := by
  change uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫
    (a.app (ofChain (ComposableArrows.mk₀ d)) ≫
      (pre (i.app d)).app (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (F.obj d)))) = _
  rw [← name_evaluate K F a d]
  exact (congrArg (fun k => uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫ k))
    (RelativeChoiceSpace.name_precomp (i.app d) (NerveMovingParameter.evaluate K F a d))).trans
      (by rw [RelativeChoiceSpace.name, Iso.inv_hom_id_assoc, uncurry'_curry'])

variable {E : Type uE} [Category.{vE} E] (H : E ⥤ D)

lemma evaluate_reindex (e : E) : NerveMovingParameter.evaluate (H ⋙ K) (H ⋙ F)
    (reindex K (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted F) H a) e =
      NerveMovingParameter.evaluate K F a (H.obj e) := by
  dsimp only [NerveMovingParameter.evaluate, reindex]
  congr 3
  apply congrArg Opposite.op
  change (nerve D).elementsMk (Opposite.op (SimplexCategory.mk 0))
    (ComposableArrows.mk₀ e ⋙ H) =
      (nerve D).elementsMk (Opposite.op (SimplexCategory.mk 0)) (ComposableArrows.mk₀ (H.obj e))
  apply congrArg ((nerve D).elementsMk (Opposite.op (SimplexCategory.mk 0)))
  change ComposableArrows.mk₀ e ⋙ H = ComposableArrows.mk₀ (H.obj e)
  exact ComposableArrows.ext₀ rfl

end SerrePositivity.SimplicialModel.NerveBiparameterMaps
