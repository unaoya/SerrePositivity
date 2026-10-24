module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.Colimit
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.LeftKanShapeIso
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.RightKanShapeIso
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LimitColimitOpposite
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
namespace SerrePositivity.InfinityCategories.F1B

variable {K C D : Type u} [Category.{u} K] [Category.{u} C] [Category.{u} D]
  (L : K ⥤ C) (F₀ : K ⥤ D) (c : C)

/-- 概要：native な左 Kan の局所余極限の存在は通常の comma の余極限と同値。
方針：左右の添字同型と nerve の余極限の比較を合成する。
規約：同じ宇宙で指定した元の関手と点を保持する。
使われ方：左 pointwise Kan の存在条件の古典比較。 -/
lemma nerve_leftKanDiagram_hasColimit_iff :
    HasColimit (leftKanDiagram (nerveMap L) (nerveMap F₀) (nerveVertex c)) ↔
      L.HasPointwiseLeftKanExtensionAt F₀ c := by
  have h := kanHasColimit_iff_restrict_of_isIso
    (leftKanDiagram (nerveMap L) (nerveMap F₀) (nerveVertex c))
    (SerrePositivity.InfinityCategories.F1B.nerveLeftKanShapeIso L c).hom
  rw [SerrePositivity.InfinityCategories.F1B.nerveLeftKanShapeIso_hom_diagram] at h
  exact h.trans SerrePositivity.InfinityCategories.F1B.nerve_hasColimit_iff

/-- 概要：native な右 Kan の局所極限の存在は通常の comma の極限と同値。
方針：左右の添字同型と nerve の極限の比較を合成する。
規約：同じ宇宙で指定した元の関手と点を保持する。
使われ方：右 pointwise Kan の存在条件の古典比較。 -/
lemma nerve_rightKanDiagram_hasLimit_iff :
    HasLimit (rightKanDiagram (nerveMap L) (nerveMap F₀) (nerveVertex c)) ↔
      L.HasPointwiseRightKanExtensionAt F₀ c := by
  have h := kanHasLimit_iff_restrict_of_isIso
    (rightKanDiagram (nerveMap L) (nerveMap F₀) (nerveVertex c))
    (SerrePositivity.InfinityCategories.F1B.nerveRightKanShapeIso c L).hom
  rw [SerrePositivity.InfinityCategories.F1B.nerveRightKanShapeIso_hom_diagram] at h
  exact h.trans SerrePositivity.InfinityCategories.F1B.nerve_hasLimit_iff

end SerrePositivity.InfinityCategories.F1B
