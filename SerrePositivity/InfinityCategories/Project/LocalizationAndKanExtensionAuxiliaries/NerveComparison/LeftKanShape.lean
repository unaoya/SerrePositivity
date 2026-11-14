module

public import SerrePositivity.InfinityCategories.HTT.Section1_2_9.OverIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes

/-!
概要：通常の左 comma の nerve から native な左 Kan 添字へ写す。
方針：Over の比較同型と二つの射影で引き戻しへ持ち上げる。
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

/-- 概要：通常の左 comma の nerve を native な左 Kan 添字へ写す。
方針：二つの射影を引き戻しへ持ち上げる。
規約：元の K を第一因子に置く。
使われ方：左 Kan の点ごとの添字の比較。 -/
def nerveLeftKanShapeMap :
    nerve (CostructuredArrow L c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (nerveMap L) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) :=
  pullback.lift (nerveMap (CostructuredArrow.proj L c))
    (nerveMap (CostructuredArrow.toOver L c) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso c).hom) (by
      rw [Category.assoc]
      erw [_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso_projection]
      rfl)

/-- 概要：左比較射は元の添字 K への射影を保つ。
方針：持ち上げの第一射影を読む。
規約：指定射影との厳密な可換性。
使われ方：元の図式の制限との照合。 -/
lemma nerveLeftKanShapeMap_projection : nerveLeftKanShapeMap L c ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection (nerveMap L) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) = nerveMap (CostructuredArrow.proj L c) :=
  pullback.lift_fst _ _ _

/-- 概要：左比較射は c へ向かう矢印の単体を保つ。
方針：引き戻しの第二射影を使う。
規約：Over と native な slice の同型を使う。
使われ方：局所余錐の辺の照合。 -/
lemma nerveLeftKanShapeMap_over : nerveLeftKanShapeMap L c ≫ pullback.snd _ _ =
    nerveMap (CostructuredArrow.toOver L c) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso c).hom :=
  pullback.lift_snd _ _ _

/-- 概要：左比較射の局所図式は通常の comma 上の制限の nerve に等しい。
方針：元の添字への射影の式を後合成する。
規約：元の図式 F₀ を固定する。
使われ方：点ごとの余極限条件の比較。 -/
lemma nerveLeftKanShapeMap_diagram {D : Type u} [Category.{u} D] (F₀ : K ⥤ D) :
    nerveLeftKanShapeMap L c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram (nerveMap L) (nerveMap F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) =
      nerveMap (CostructuredArrow.proj L c ⋙ F₀) := by
  change nerveLeftKanShapeMap L c ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection _ _ ≫ nerveMap F₀) = _
  rw [← Category.assoc, nerveLeftKanShapeMap_projection]
  rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
