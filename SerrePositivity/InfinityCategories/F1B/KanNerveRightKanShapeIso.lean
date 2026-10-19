module

public import SerrePositivity.InfinityCategories.F1B.KanStructuredArrowPullback
public import SerrePositivity.InfinityCategories.F1B.KanNerveRightKanShape
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
namespace SerrePositivity.InfinityCategories.F1B

variable {K C : Type u} [Category.{u} K] [Category.{u} C]
variable (c : C) (L : K ⥤ C)

/-- 概要：通常の右 comma の引き戻しは nerve によって保存される。
方針：nerve が右随伴であることから極限保存を使う。
規約：単体集合の厳密な引き戻し。
使われ方：native な局所添字への同定。 -/
lemma kanNerveStructuredArrow_isPullback : IsPullback (nerveMap (StructuredArrow.toUnder c L))
    (nerveMap (StructuredArrow.proj c L)) (nerveMap (Under.forget c)) (nerveMap L) :=
  (kanStructuredArrow_isPullback c L).map nerveFunctor

/-- 概要：Under の比較射を合成した右 comma の四角形は引き戻し。
方針：Under の nerve と native な coslice の同型で移送する。
規約：既存の比較射の二つの射影をそのまま使う。
使われ方：元の右 Kan 比較射の同型性。 -/
lemma kanNerveRightKanShape_isPullback : IsPullback
    (nerveMap (StructuredArrow.toUnder c L) ≫ kanNerveUnderMap c)
    (nerveMap (StructuredArrow.proj c L)) (sliceUnderProjection (nervePoint c)) (nerveMap L) := by
  exact (kanNerveStructuredArrow_isPullback c L).of_iso (Iso.refl _)
    (kanNerveUnderIso c) (Iso.refl _) (Iso.refl _)
    (by change _ ≫ kanNerveUnderMap c = 𝟙 _ ≫ (_ ≫ kanNerveUnderMap c); simp)
    (by simp)
    (by change nerveMap (Under.forget c) ≫ 𝟙 _ = kanNerveUnderMap c ≫ _
        rw [Category.comp_id]
        exact (kanNerveUnderMap_projection c).symm)
    (by simp)

/-- 概要：通常の右 comma から native な右 Kan 添字への比較射は同型。
方針：引き戻しの普遍同型と二つの射影で同定する。
規約：元の指定比較射そのものの同型性。
使われ方：局所図式と局所錐の古典比較。 -/
instance kanNerveRightKanShapeMap_isIso : IsIso (kanNerveRightKanShapeMap L c) := by
  have he : kanNerveRightKanShapeMap L c =
      (kanNerveRightKanShape_isPullback c L).isoPullback.hom := by
    apply pullback.hom_ext
    · rw [kanNerveRightKanShapeMap_under]
      exact ((kanNerveRightKanShape_isPullback c L).isoPullback_hom_fst).symm
    · rw [kanNerveRightKanShapeMap_projection]
      exact ((kanNerveRightKanShape_isPullback c L).isoPullback_hom_snd).symm
  rw [he]
  infer_instance


/-- 概要：通常の右 comma の nerve と native な右 Kan 添字の指定同型。
方針：元の比較射とその同型性をまとめる。
規約：順方向は射影と局所図式を保つ既存の比較射。
使われ方：点ごとの極限条件の古典比較。 -/
def kanNerveRightKanShapeIso :
    nerve (StructuredArrow c L) ≅ rightKanShape (nerveMap L) (nerveVertex c) :=
  asIso (kanNerveRightKanShapeMap L c)

/-- 概要：右 Kan 添字の指定同型は元の添字への射影を保つ。
方針：同型の順方向の比較射の式を使う。
規約：射影の厳密な等式。
使われ方：局所錐を同じ元の図式へ制限する。 -/
lemma kanNerveRightKanShapeIso_hom_projection :
    (kanNerveRightKanShapeIso c L).hom ≫ rightKanProjection (nerveMap L) (nerveVertex c) =
      nerveMap (StructuredArrow.proj c L) := kanNerveRightKanShapeMap_projection L c

/-- 概要：右 Kan 添字の指定同型は通常の局所図式の nerve を保つ。
方針：元の比較射と局所図式の可換性を読む。
規約：指定した元の図式 F₀ を変更しない。
使われ方：点ごとの極限条件の比較。 -/
lemma kanNerveRightKanShapeIso_hom_diagram {D : Type u} [Category.{u} D] (F₀ : K ⥤ D) :
    (kanNerveRightKanShapeIso c L).hom ≫
      rightKanDiagram (nerveMap L) (nerveMap F₀) (nerveVertex c) =
        nerveMap (StructuredArrow.proj c L ⋙ F₀) := kanNerveRightKanShapeMap_diagram L F₀ c

end SerrePositivity.InfinityCategories.F1B
