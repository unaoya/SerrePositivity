module

public import SerrePositivity.InfinityCategories.F1B.KanCostructuredArrowPullback
public import SerrePositivity.InfinityCategories.F1B.KanNerveLeftKanShape
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
namespace SerrePositivity.InfinityCategories.F1B

variable {K C : Type u} [Category.{u} K] [Category.{u} C]
variable (L : K ⥤ C) (c : C)

/-- 概要：通常の左 comma の引き戻しは nerve で保存される。
方針：nerve の極限保存を使う。
規約：単体集合の厳密な引き戻し。
使われ方：native な左 Kan 添字の同定。 -/
lemma kanNerveCostructuredArrow_isPullback : IsPullback (nerveMap (CostructuredArrow.toOver L c))
    (nerveMap (CostructuredArrow.proj L c)) (nerveMap (Over.forget c)) (nerveMap L) :=
  (kanCostructuredArrow_isPullback L c).map nerveFunctor

/-- 概要：左 comma と native な slice の四角形は引き戻し。
方針：Over の比較同型で移送し因子の順序を交換する。
規約：元の添字 K を第一因子に置く。
使われ方：元の左 Kan 比較射の同型性。 -/
lemma kanNerveLeftKanShape_isPullback : IsPullback (nerveMap (CostructuredArrow.proj L c))
    (nerveMap (CostructuredArrow.toOver L c) ≫ (kanNerveOverIso c).hom)
    (nerveMap L) (sliceOverProjection (nervePoint c)) := by
  exact ((kanNerveCostructuredArrow_isPullback L c).of_iso (Iso.refl _)
    (kanNerveOverIso c) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simpa using (kanNerveOverIso_projection c).symm) (by simp)).flip

/-- 概要：通常の左 comma から native な左 Kan 添字への比較射は同型。
方針：引き戻しの普遍同型と二つの射影で同定する。
規約：指定比較射そのものの同型性を証明する。
使われ方：局所図式と局所余錐の古典比較。 -/
instance kanNerveLeftKanShapeMap_isIso : IsIso (kanNerveLeftKanShapeMap L c) := by
  have he : kanNerveLeftKanShapeMap L c =
      (kanNerveLeftKanShape_isPullback L c).isoPullback.hom := by
    apply pullback.hom_ext
    · rw [kanNerveLeftKanShapeMap_projection]
      exact ((kanNerveLeftKanShape_isPullback L c).isoPullback_hom_fst).symm
    · rw [kanNerveLeftKanShapeMap_over]
      exact ((kanNerveLeftKanShape_isPullback L c).isoPullback_hom_snd).symm
  rw [he]
  infer_instance

/-- 概要：通常の左 comma の nerve と native な左 Kan 添字の指定同型。
方針：元の比較射とその同型性をまとめる。
規約：順方向は射影と局所図式を保つ既存の比較射。
使われ方：点ごとの余極限条件の比較。 -/
def kanNerveLeftKanShapeIso :
    nerve (CostructuredArrow L c) ≅ leftKanShape (nerveMap L) (nerveVertex c) :=
  asIso (kanNerveLeftKanShapeMap L c)


/-- 概要：左 Kan 添字の指定同型は元の添字への射影を保つ。
方針：同型の順方向の比較射の式を使う。
規約：元の K への射影の厳密な等式。
使われ方：局所余錐を同じ図式へ制限する。 -/
lemma kanNerveLeftKanShapeIso_hom_projection :
    (kanNerveLeftKanShapeIso L c).hom ≫ leftKanProjection (nerveMap L) (nerveVertex c) =
      nerveMap (CostructuredArrow.proj L c) := kanNerveLeftKanShapeMap_projection L c


/-- 概要：左 Kan 添字の指定同型は通常の局所図式の nerve を保つ。
方針：元の比較射と局所図式の可換性を使う。
規約：元の図式 F₀ を固定する。
使われ方：点ごとの余極限条件の比較。 -/
lemma kanNerveLeftKanShapeIso_hom_diagram {D : Type u} [Category.{u} D] (F₀ : K ⥤ D) :
    (kanNerveLeftKanShapeIso L c).hom ≫
      leftKanDiagram (nerveMap L) (nerveMap F₀) (nerveVertex c) =
        nerveMap (CostructuredArrow.proj L c ⋙ F₀) := kanNerveLeftKanShapeMap_diagram L c F₀

end SerrePositivity.InfinityCategories.F1B
