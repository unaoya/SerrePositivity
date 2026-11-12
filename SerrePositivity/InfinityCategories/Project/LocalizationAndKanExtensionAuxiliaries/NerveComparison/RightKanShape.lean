module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes

/-!
概要：右 Kan 拡張の通常の comma 圏から native な局所添字へ比較射を構成する。
方針：Under の nerve の同型と引き戻しへの持ち上げを使う。
規約：射影と元の局所図式を厳密に保つ比較。
使われ方：B5 の pointwise Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {K C D : Type u} [Category.{u} K] [Category.{u} C] [Category.{u} D]

/-- 概要：通常の右 comma の nerve から native な右 Kan の添字へ写す。
方針：Under の比較射と二つの標準射影で引き戻しへ持ち上げる。
規約：比較の同型性はこの定義では主張しない。
使われ方：pointwise Kan の局所添字の比較。 -/
def nerveRightKanShapeMap (L : K ⥤ C) (c : C) :
    nerve (StructuredArrow c L) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape (nerveMap L) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) :=
  pullback.lift (nerveMap (StructuredArrow.toUnder c L) ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderMap c)
    (nerveMap (StructuredArrow.proj c L)) (by
      rw [Category.assoc]
      erw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderMap_projection]
      rfl)

/-- 概要：比較射は元の K への射影を保つ。
方針：引き戻しへの持ち上げの第二射影を読む。
規約：指定された射影との厳密な可換性。
使われ方：元の図式の制限との照合。 -/
lemma nerveRightKanShapeMap_projection (L : K ⥤ C) (c : C) :
    nerveRightKanShapeMap L c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection (nerveMap L) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) =
      nerveMap (StructuredArrow.proj c L) := pullback.lift_snd _ _ _

/-- 概要：比較射は c からの矢印の単体を保つ。
方針：引き戻しの第一射影の式を使う。
規約：Under の nerve の比較射を使う。
使われ方：局所錐の先端と辺の照合。 -/
lemma nerveRightKanShapeMap_under (L : K ⥤ C) (c : C) :
    nerveRightKanShapeMap L c ≫ pullback.fst _ _ =
      nerveMap (StructuredArrow.toUnder c L) ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderMap c := pullback.lift_fst _ _ _

/-- 概要：局所図式への比較は通常の comma 上の制限の nerve に等しい。
方針：元の添字への射影との可換性を後合成する。
規約：通常の元の図式 F₀ を固定する。
使われ方：点ごとの極限条件の古典比較。 -/
lemma nerveRightKanShapeMap_diagram (L : K ⥤ C) (F₀ : K ⥤ D) (c : C) :
    nerveRightKanShapeMap L c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (nerveMap L) (nerveMap F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) =
      nerveMap (StructuredArrow.proj c L ⋙ F₀) := by
  change nerveRightKanShapeMap L c ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection _ _ ≫ nerveMap F₀) = _
  rw [← Category.assoc, nerveRightKanShapeMap_projection]
  rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
