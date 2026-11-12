module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.KanLocalExistence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaCoconeColimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightExistence

/-!
概要：nerve 上の Kan 拡張の存在を通常の pointwise Kan の存在と比較する。
方針：全頂点での局所存在条件を通常の圏の全対象での条件へ移す。
規約：存在する拡張の単位や余単位を事前には指定しない。
使われ方：B5 の点ごとの存在と大域的組み立ての古典比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {K C D : Type u} [Category.{u} K] [Category.{u} C] [Category.{u} D]
  (L : K ⥤ C) (F₀ : K ⥤ D)

/-- 概要：nerve 上の左 Kan 拡張の存在は通常の pointwise 左 Kan の存在と同値。
方針：全頂点の局所余極限判定と通常の comma 図式の比較を使う。
規約：大域的な Hom 普遍性だけによる一般の Kan 拡張と区別する。
使われ方：B5 の左 Kan の点ごとの存在条件の回収。 -/
lemma nerve_exists_leftKan_iff_pointwise :
    (∃ (F : nerve C ⟶ nerve D) (β : SSet.Homotopy (nerveMap F₀) (nerveMap L ≫ F)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (nerveMap L) (nerveMap F₀) F β) ↔
        L.HasPointwiseLeftKanExtension F₀ := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_iff_local_colimits]
  constructor
  · intro h c
    exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerve_leftKanDiagram_hasColimit_iff L F₀ c).1 (h (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))
  · intro h v
    obtain ⟨c, rfl⟩ := (nerveEquiv (C := C)).symm.surjective v
    exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerve_leftKanDiagram_hasColimit_iff L F₀ c).2 (h c)

/-- 概要：nerve 上の右 Kan 拡張の存在は通常の pointwise 右 Kan の存在と同値。
方針：全頂点の局所極限判定と通常の comma 図式の比較を使う。
規約：大域的な Hom 普遍性だけによる一般の Kan 拡張と区別する。
使われ方：B5 の右 Kan の点ごとの存在条件の回収。 -/
lemma nerve_exists_rightKan_iff_pointwise :
    (∃ (F : nerve C ⟶ nerve D) (α : SSet.Homotopy (nerveMap L ≫ F) (nerveMap F₀)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension (nerveMap L) (nerveMap F₀) F α) ↔
        L.HasPointwiseRightKanExtension F₀ := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRightExtension_iff_local_limits]
  constructor
  · intro h c
    exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerve_rightKanDiagram_hasLimit_iff L F₀ c).1 (h (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))
  · intro h v
    obtain ⟨c, rfl⟩ := (nerveEquiv (C := C)).symm.surjective v
    exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerve_rightKanDiagram_hasLimit_iff L F₀ c).2 (h c)

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
