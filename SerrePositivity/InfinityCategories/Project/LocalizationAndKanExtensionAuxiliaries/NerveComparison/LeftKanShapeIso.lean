module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.CostructuredArrowPullback
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.LeftKanShape
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：通常の左 comma の nerve と native な左 Kan 添字を同型にする。
方針：左 comma の引き戻しを nerve と Over の比較同型で移す。
規約：同じ宇宙の小さい圏を扱う。
使われ方：B5 の左 Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {K C : Type u} [Category.{u} K] [Category.{u} C]
variable (L : K ⥤ C) (c : C)

/-- 概要：通常の左 comma の引き戻しは nerve で保存される。
方針：nerve の極限保存を使う。
規約：単体集合の厳密な引き戻し。
使われ方：native な左 Kan 添字の同定。 -/
lemma nerveCostructuredArrow_isPullback : IsPullback (nerveMap (CostructuredArrow.toOver L c))
    (nerveMap (CostructuredArrow.proj L c)) (nerveMap (Over.forget c)) (nerveMap L) :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.costructuredArrow_isPullback L c).map nerveFunctor

/-- 概要：左 comma と native な slice の四角形は引き戻し。
方針：Over の比較同型で移送し因子の順序を交換する。
規約：元の添字 K を第一因子に置く。
使われ方：元の左 Kan 比較射の同型性。 -/
lemma nerveLeftKanShape_isPullback : IsPullback (nerveMap (CostructuredArrow.proj L c))
    (nerveMap (CostructuredArrow.toOver L c) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso c).hom)
    (nerveMap L) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c)) := by
  exact ((nerveCostructuredArrow_isPullback L c).of_iso (Iso.refl _)
    (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso c) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simpa using (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso_projection c).symm) (by simp)).flip

/-- 概要：通常の左 comma から native な左 Kan 添字への比較射は同型。
方針：引き戻しの普遍同型と二つの射影で同定する。
規約：指定比較射そのものの同型性を証明する。
使われ方：局所図式と局所余錐の古典比較。 -/
instance nerveLeftKanShapeMap_isIso : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeMap L c) := by
  have he : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeMap L c =
      (nerveLeftKanShape_isPullback L c).isoPullback.hom := by
    apply pullback.hom_ext
    · rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeMap_projection]
      exact ((nerveLeftKanShape_isPullback L c).isoPullback_hom_fst).symm
    · rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeMap_over]
      exact ((nerveLeftKanShape_isPullback L c).isoPullback_hom_snd).symm
  rw [he]
  infer_instance

/-- 概要：通常の左 comma の nerve と native な左 Kan 添字の指定同型。
方針：元の比較射とその同型性をまとめる。
規約：順方向は射影と局所図式を保つ既存の比較射。
使われ方：点ごとの余極限条件の比較。 -/
def nerveLeftKanShapeIso :
    nerve (CostructuredArrow L c) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (nerveMap L) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) :=
  asIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeMap L c)


/-- 概要：左 Kan 添字の指定同型は元の添字への射影を保つ。
方針：同型の順方向の比較射の式を使う。
規約：元の K への射影の厳密な等式。
使われ方：局所余錐を同じ図式へ制限する。 -/
lemma nerveLeftKanShapeIso_hom_projection :
    (nerveLeftKanShapeIso L c).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection (nerveMap L) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) =
      nerveMap (CostructuredArrow.proj L c) := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeMap_projection L c


/-- 概要：左 Kan 添字の指定同型は通常の局所図式の nerve を保つ。
方針：元の比較射と局所図式の可換性を使う。
規約：元の図式 F₀ を固定する。
使われ方：点ごとの余極限条件の比較。 -/
lemma nerveLeftKanShapeIso_hom_diagram {D : Type u} [Category.{u} D] (F₀ : K ⥤ D) :
    (nerveLeftKanShapeIso L c).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram (nerveMap L) (nerveMap F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) =
        nerveMap (CostructuredArrow.proj L c ⋙ F₀) := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeMap_diagram L c F₀

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
