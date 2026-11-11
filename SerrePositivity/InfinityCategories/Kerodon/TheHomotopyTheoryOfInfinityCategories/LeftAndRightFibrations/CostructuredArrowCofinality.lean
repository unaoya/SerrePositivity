module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibrationCofinalPullback
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.LeftKanShapeIso

/-!
# 元の分解の余終性を固定右脚の costructured arrow へ移す

概要：Low 命題 3.7 の各固定右脚の比較射の nerve の余終性を与える。
方針：元の comma の射影を native な slice の right fibration と比較して引き戻す。
規約：同じ宇宙の小圏で元の関手・中間射・比較射を保持する。
使われ方：三本矢の右変数の全図式の成分ごとの余終性。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories

variable {K L C : Type u} [Category.{u} K] [Category.{u} L] [Category.{u} C]

/-- 概要：元の costructured arrow の nerve の射影は right fibration（Low 命題 3.7）。
方針：元の comma と native な slice の引き戻し正方形を使う。
規約：元の comma の全射を保持する。
使われ方：分解の余終性の底変換。 -/
lemma costructuredArrowProjection_rightFibration (Q : L ⥤ C) (V : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (nerveMap (CostructuredArrow.proj Q V)) := by
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.of_isPullback (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShape_isPullback Q V).flip
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint V)))⟩

/-- 概要：元の固定右脚の比較の nerve は分解図式の引き戻し（Low 命題 3.7）。
方針：元の二つの comma の引き戻し正方形を貼り合わせて消去する。
規約：上射は元の CostructuredArrow.pre の nerve そのもの。
使われ方：固定した右脚の比較の余終性の判定。 -/
lemma costructuredArrowPre_isPullback (P : K ⥤ L) (Q : L ⥤ C) (V : C) :
    IsPullback (nerveMap (CostructuredArrow.pre P Q V))
      (nerveMap (CostructuredArrow.proj (P ⋙ Q) V))
      (nerveMap (CostructuredArrow.proj Q V)) (nerveMap P) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveCostructuredArrow_isPullback (P ⋙ Q) V
  change IsPullback (nerveMap (CostructuredArrow.pre P Q V) ≫
      nerveMap (CostructuredArrow.toOver Q V))
    (nerveMap (CostructuredArrow.proj (P ⋙ Q) V)) (nerveMap (Over.forget V))
    (nerveMap P ≫ nerveMap Q) at h
  exact h.of_right (by rfl) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveCostructuredArrow_isPullback Q V)

/-- 概要：分解の余終性は各固定右脚の比較に保たれる（Low 命題 3.7）。
方針：元の costructured arrow の right fibration に沿って分解を引き戻す。
規約：元の指定した比較射の left cofinality を主張する。
使われ方：右脚の全図式の成分ごとの比較。 -/
lemma costructuredArrowPre_isLeftCofinal (P : K ⥤ L) (Q : L ⥤ C) (V : C)
    (hP : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap P)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap (CostructuredArrow.pre P Q V)) := by
  have := costructuredArrowProjection_rightFibration Q V
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibration_isPullback_isLeftCofinal (costructuredArrowPre_isPullback P Q V) hP

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
