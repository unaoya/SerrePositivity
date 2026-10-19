module

public import SerrePositivity.InfinityCategories.F1B.KanNerveRightCanonicalCone
public import SerrePositivity.InfinityCategories.F1B.KanNerveConePostcomposeHomotopy
public import SerrePositivity.InfinityCategories.F1B.KanExtension
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
概要：指定余単位に沿う通常の右 Kan 局所錐を native な輸送として表示する。
方針：標準錐からの脚の後合成ホモトピーを comma の添字同型で移す。
規約：元の図式・指定余単位・錐の頂点を固定する。
使われ方：B5 の通常の pointwise 右 Kan の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {K C D : Type u} [Category.{u} K] [Category.{u} C] [Category.{u} D]
  (L : K ⥤ C) {F₀ : K ⥤ D} {F : C ⥤ D} (α : L ⋙ F ⟶ F₀) (c : C)

/-- 概要：右 Kan の標準錐の比較を添字の逆同型へ移す。
方針：通常の錐の後合成を添字同型で移し、両端・図式・頂点を照合する。
規約：元の指定余単位を全時間で保持する。
使われ方：B5 の pointwise 右 Kan 条件の双方向比較。 -/
lemma kanNerveRightKanCanonicalCone_inv :
    joinMap (𝟙 (Δ[0] : SSet.{u})) (kanNerveRightKanShapeIso c L).inv ≫
    (kanNerveCone (kanClassicalRightKanCanonicalCone L F c)).val =
      (rightKanCanonicalCone (nerveMap L) (nerveMap F) (nerveVertex c)).val := by
  rw [← kanNerveRightKanCanonicalCone, ← Category.assoc, ← joinMap_comp,
    Category.id_comp, Iso.inv_hom_id, joinMap_id, Category.id_comp]

/-- 概要：指定余単位の通常の局所錐から native な右 Kan の輸送を構成する。
方針：通常の錐の後合成を添字同型で移し、両端・図式・頂点を照合する。
規約：元の指定余単位を全時間で保持する。
使われ方：B5 の pointwise 右 Kan 条件の双方向比較。 -/
def kanNerveRightConeTransport : RightKanConeTransport (nerveMap L) (nerveMap F₀) (nerveMap F)
    (kanNerveNatTransHomotopy α) (nerveVertex c) where
  family := (joinMap (𝟙 (Δ[0] : SSet.{u})) (kanNerveRightKanShapeIso c L).inv ▷ Δ[1]) ≫
    (kanNerveConePostcomposeHomotopy (kanClassicalRightKanCanonicalCone L F c)
      (Functor.whiskerLeft (StructuredArrow.proj c L) α)).h
  start := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, SSet.Homotopy.h₀]
    exact kanNerveRightKanCanonicalCone_inv L c
  diagram := by
    rw [← Category.assoc, ← comp_whiskerRight, joinInr_joinMap, comp_whiskerRight,
      Category.assoc, kanNerveConePostcomposeHomotopy_diagram,
      ← kanNerveNatTransHomotopy_whiskerLeft, ← Category.assoc, ← comp_whiskerRight]
    have hp : (kanNerveRightKanShapeIso c L).inv ≫
        nerveMap (StructuredArrow.proj c L) = rightKanProjection (nerveMap L) (nerveVertex c) := by
      rw [← kanNerveRightKanShapeIso_hom_projection, Iso.inv_hom_id_assoc]
    rw [hp]
  fixedVertex := by
    rw [← Category.assoc, ← comp_whiskerRight, joinInl_joinMap, Category.id_comp,
      kanNerveConePostcomposeHomotopy_fixedVertex]
    have hj : joinInl (Δ[0] : SSet.{u}) (rightKanShape (nerveMap L) (nerveVertex c)) ≫
        joinMap (𝟙 (Δ[0] : SSet.{u})) (kanNerveRightKanShapeIso c L).inv =
          joinInl (Δ[0] : SSet.{u}) (nerve (StructuredArrow c L)) := by
      rw [joinInl_joinMap, Category.id_comp]
    rw [← hj, Category.assoc, kanNerveRightKanCanonicalCone_inv]

/-- 概要：輸送後の錐は通常の指定余単位の局所錐の nerve と一致する。
方針：通常の錐の後合成を添字同型で移し、両端・図式・頂点を照合する。
規約：元の指定余単位を全時間で保持する。
使われ方：B5 の pointwise 右 Kan 条件の双方向比較。 -/
lemma kanNerveRightConeTransport_cone :
    joinMap (𝟙 (Δ[0] : SSet.{u})) (kanNerveRightKanShapeIso c L).hom ≫
      (kanNerveRightConeTransport L α c).cone.val =
        (kanNerveCone ((Functor.RightExtension.mk F α).coneAt c)).val := by
  change joinMap (𝟙 (Δ[0] : SSet.{u})) (kanNerveRightKanShapeIso c L).hom ≫
    (SSet.ι₁ ≫ (joinMap (𝟙 (Δ[0] : SSet.{u})) (kanNerveRightKanShapeIso c L).inv ▷ Δ[1]) ≫
      (kanNerveConePostcomposeHomotopy (kanClassicalRightKanCanonicalCone L F c)
        (Functor.whiskerLeft (StructuredArrow.proj c L) α)).h) = _
  rw [← Category.assoc (SSet.ι₁), SSet.ι₁_comp, Category.assoc, SSet.Homotopy.h₁,
    ← Category.assoc, ← joinMap_comp, Category.id_comp, Iso.hom_inv_id,
    joinMap_id, Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories.F1B
