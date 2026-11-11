module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Colimit
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.LeftKanShapeIso
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.RightKanShapeIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LimitColimitOpposite
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
概要：Kan 拡張の native な局所存在条件を通常の comma 図式と比較する。
方針：左右の添字同型で制限し nerve の極限・余極限の存在判定を使う。
規約：点ごとの存在と指定単位・余単位の普遍性は区別する。
使われ方：B5 の通常の pointwise Kan の存在条件の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {K C D : Type u} [Category.{u} K] [Category.{u} C] [Category.{u} D]
  (L : K ⥤ C) (F₀ : K ⥤ D) (c : C)

/-- 概要：native な左 Kan の局所余極限の存在は通常の comma の余極限と同値。
方針：左右の添字同型と nerve の余極限の比較を合成する。
規約：同じ宇宙で指定した元の関手と点を保持する。
使われ方：左 pointwise Kan の存在条件の古典比較。 -/
lemma nerve_leftKanDiagram_hasColimit_iff :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram (nerveMap L) (nerveMap F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) ↔
      L.HasPointwiseLeftKanExtensionAt F₀ c := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasColimit_iff_restrict_of_isIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram (nerveMap L) (nerveMap F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso L c).hom
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso_hom_diagram] at h
  exact h.trans _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerve_hasColimit_iff

/-- 概要：native な右 Kan の局所極限の存在は通常の comma の極限と同値。
方針：左右の添字同型と nerve の極限の比較を合成する。
規約：同じ宇宙で指定した元の関手と点を保持する。
使われ方：右 pointwise Kan の存在条件の古典比較。 -/
lemma nerve_rightKanDiagram_hasLimit_iff :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (nerveMap L) (nerveMap F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) ↔
      L.HasPointwiseRightKanExtensionAt F₀ c := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasLimit_iff_restrict_of_isIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (nerveMap L) (nerveMap F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeIso c L).hom
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeIso_hom_diagram] at h
  exact h.trans _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerve_hasLimit_iff

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
