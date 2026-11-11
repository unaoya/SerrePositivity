module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.StructuredArrowPullback
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.RightKanShape
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：通常の右 comma の nerve と native な右 Kan 添字を同型にする。
方針：通常の引き戻しを nerve に写し Under の coslice 表示を使う。
規約：同じ宇宙の小さい圏を扱う。
使われ方：B5 の pointwise Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {K C : Type u} [Category.{u} K] [Category.{u} C]
variable (c : C) (L : K ⥤ C)

/-- 概要：通常の右 comma の引き戻しは nerve によって保存される。
方針：nerve が右随伴であることから極限保存を使う。
規約：単体集合の厳密な引き戻し。
使われ方：native な局所添字への同定。 -/
lemma nerveStructuredArrow_isPullback : IsPullback (nerveMap (StructuredArrow.toUnder c L))
    (nerveMap (StructuredArrow.proj c L)) (nerveMap (Under.forget c)) (nerveMap L) :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.structuredArrow_isPullback c L).map nerveFunctor

/-- 概要：Under の比較射を合成した右 comma の四角形は引き戻し。
方針：Under の nerve と native な coslice の同型で移送する。
規約：既存の比較射の二つの射影をそのまま使う。
使われ方：元の右 Kan 比較射の同型性。 -/
lemma nerveRightKanShape_isPullback : IsPullback
    (nerveMap (StructuredArrow.toUnder c L) ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderMap c)
    (nerveMap (StructuredArrow.proj c L)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c)) (nerveMap L) := by
  exact (nerveStructuredArrow_isPullback c L).of_iso (Iso.refl _)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderIso c) (Iso.refl _) (Iso.refl _)
    (by change _ ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderMap c = 𝟙 _ ≫ (_ ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderMap c); simp)
    (by simp)
    (by change nerveMap (Under.forget c) ≫ 𝟙 _ = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderMap c ≫ _
        rw [Category.comp_id]
        exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderMap_projection c).symm)
    (by simp)

/-- 概要：通常の右 comma から native な右 Kan 添字への比較射は同型。
方針：引き戻しの普遍同型と二つの射影で同定する。
規約：元の指定比較射そのものの同型性。
使われ方：局所図式と局所錐の古典比較。 -/
instance nerveRightKanShapeMap_isIso : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeMap L c) := by
  have he : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeMap L c =
      (nerveRightKanShape_isPullback c L).isoPullback.hom := by
    apply pullback.hom_ext
    · rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeMap_under]
      exact ((nerveRightKanShape_isPullback c L).isoPullback_hom_fst).symm
    · rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeMap_projection]
      exact ((nerveRightKanShape_isPullback c L).isoPullback_hom_snd).symm
  rw [he]
  infer_instance


/-- 概要：通常の右 comma の nerve と native な右 Kan 添字の指定同型。
方針：元の比較射とその同型性をまとめる。
規約：順方向は射影と局所図式を保つ既存の比較射。
使われ方：点ごとの極限条件の古典比較。 -/
def nerveRightKanShapeIso :
    nerve (StructuredArrow c L) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape (nerveMap L) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) :=
  asIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeMap L c)

/-- 概要：右 Kan 添字の指定同型は元の添字への射影を保つ。
方針：同型の順方向の比較射の式を使う。
規約：射影の厳密な等式。
使われ方：局所錐を同じ元の図式へ制限する。 -/
lemma nerveRightKanShapeIso_hom_projection :
    (nerveRightKanShapeIso c L).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection (nerveMap L) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) =
      nerveMap (StructuredArrow.proj c L) := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeMap_projection L c

/-- 概要：右 Kan 添字の指定同型は通常の局所図式の nerve を保つ。
方針：元の比較射と局所図式の可換性を読む。
規約：指定した元の図式 F₀ を変更しない。
使われ方：点ごとの極限条件の比較。 -/
lemma nerveRightKanShapeIso_hom_diagram {D : Type u} [Category.{u} D] (F₀ : K ⥤ D) :
    (nerveRightKanShapeIso c L).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (nerveMap L) (nerveMap F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) =
        nerveMap (StructuredArrow.proj c L ⋙ F₀) := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeMap_diagram L F₀ c

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
