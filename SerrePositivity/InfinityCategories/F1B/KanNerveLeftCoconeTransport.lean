module

public import SerrePositivity.InfinityCategories.F1B.KanNerveLeftCanonicalCocone
public import SerrePositivity.InfinityCategories.F1B.KanNerveCoconePrecomposeHomotopy
public import SerrePositivity.InfinityCategories.F1B.KanExtension
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
概要：指定単位に沿う通常の左 Kan 局所余錐を native な輸送として表示する。
方針：標準余錐への脚の前合成ホモトピーを comma の添字同型で移す。
規約：元の図式・指定単位・余錐の頂点を固定する。
使われ方：B5 の通常の pointwise 左 Kan の回収。
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
  (L : K ⥤ C) {F₀ : K ⥤ D} {F : C ⥤ D} (β : F₀ ⟶ L ⋙ F) (c : C)

/-- 概要：左 Kan の標準余錐の比較を添字の逆同型へ移す。
方針：余錐の前合成ホモトピーを添字同型と積の交換で移す。
規約：元の指定単位と余錐の頂点を全時間で保持する。
使われ方：B5 の pointwise 左 Kan 条件の双方向比較。 -/
lemma kanNerveLeftKanCanonicalCocone_inv :
    joinMap (kanNerveLeftKanShapeIso L c).inv (𝟙 (Δ[0] : SSet.{u})) ≫
    (kanNerveCoconeEquiv (kanClassicalLeftKanCanonicalCocone L F c)).val =
      (leftKanCanonicalCocone (nerveMap L) (nerveMap F) (nerveVertex c)).val := by
  rw [← kanNerveLeftKanCanonicalCocone, ← Category.assoc, ← joinMap_comp,
    Category.id_comp, Iso.inv_hom_id, joinMap_id, Category.id_comp]

/-- 概要：指定単位の通常の局所余錐から native な左 Kan の輸送を構成する。
方針：余錐の前合成ホモトピーを添字同型と積の交換で移す。
規約：元の指定単位と余錐の頂点を全時間で保持する。
使われ方：B5 の pointwise 左 Kan 条件の双方向比較。 -/
def kanNerveLeftCoconeTransport : LeftKanCoconeTransport (nerveMap L) (nerveMap F₀) (nerveMap F)
    (kanNerveNatTransHomotopy β) (nerveVertex c) where
  family := (β_ (Δ[1] : SSet.{u}) (join (leftKanShape (nerveMap L) (nerveVertex c)) Δ[0])).hom ≫
    (joinMap (kanNerveLeftKanShapeIso L c).inv (𝟙 (Δ[0] : SSet.{u})) ▷ Δ[1]) ≫
      (kanNerveCoconePrecomposeHomotopy (kanClassicalLeftKanCanonicalCocone L F c)
        (Functor.whiskerLeft (CostructuredArrow.proj L c) β)).h
  finish := by
    rw [← Category.assoc, prismEndpoint_one_braiding, ← Category.assoc, SSet.ι₁_comp,
      Category.assoc, SSet.Homotopy.h₁]
    exact kanNerveLeftKanCanonicalCocone_inv L c
  diagram := by
    rw [← Category.assoc, BraidedCategory.braiding_naturality_right, Category.assoc,
      ← Category.assoc (joinInl _ _ ▷ Δ[1]), ← comp_whiskerRight,
      joinInl_joinMap, comp_whiskerRight, Category.assoc,
      kanNerveCoconePrecomposeHomotopy_diagram,
      ← kanNerveNatTransHomotopy_whiskerLeft, ← Category.assoc (_ ▷ Δ[1]),
      ← comp_whiskerRight]
    have hp : (kanNerveLeftKanShapeIso L c).inv ≫ nerveMap (CostructuredArrow.proj L c) =
        leftKanProjection (nerveMap L) (nerveVertex c) := by
      rw [← kanNerveLeftKanShapeIso_hom_projection, Iso.inv_hom_id_assoc]
    rw [hp]
  fixedVertex := by
    rw [← Category.assoc, BraidedCategory.braiding_naturality_right, Category.assoc,
      ← Category.assoc (joinInr _ _ ▷ Δ[1]), ← comp_whiskerRight,
      joinInr_joinMap, Category.id_comp, kanNerveCoconePrecomposeHomotopy_fixedVertex]
    change snd (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫
      joinInr (nerve (CostructuredArrow L c)) (Δ[0] : SSet.{u}) ≫
        (kanNerveCoconeEquiv (kanClassicalLeftKanCanonicalCocone L F c)).val = _
    have hj : joinInr (leftKanShape (nerveMap L) (nerveVertex c)) (Δ[0] : SSet.{u}) ≫
        joinMap (kanNerveLeftKanShapeIso L c).inv (𝟙 (Δ[0] : SSet.{u})) =
          joinInr (nerve (CostructuredArrow L c)) (Δ[0] : SSet.{u}) := by
      rw [joinInr_joinMap, Category.id_comp]
    rw [← hj, Category.assoc, kanNerveLeftKanCanonicalCocone_inv]

/-- 概要：輸送後の余錐は通常の指定単位の局所余錐の nerve と一致する。
方針：余錐の前合成ホモトピーを添字同型と積の交換で移す。
規約：元の指定単位と余錐の頂点を全時間で保持する。
使われ方：B5 の pointwise 左 Kan 条件の双方向比較。 -/
lemma kanNerveLeftCoconeTransport_cocone :
    joinMap (kanNerveLeftKanShapeIso L c).hom (𝟙 (Δ[0] : SSet.{u})) ≫
      (kanNerveLeftCoconeTransport L β c).cocone.val =
        (kanNerveCoconeEquiv ((Functor.LeftExtension.mk F β).coconeAt c)).val := by
  change joinMap (kanNerveLeftKanShapeIso L c).hom (𝟙 (Δ[0] : SSet.{u})) ≫
    (prismEndpoint 0 _ ≫ (β_ (Δ[1] : SSet.{u}) _).hom ≫
      (joinMap (kanNerveLeftKanShapeIso L c).inv (𝟙 (Δ[0] : SSet.{u})) ▷ Δ[1]) ≫
        (kanNerveCoconePrecomposeHomotopy (kanClassicalLeftKanCanonicalCocone L F c)
          (Functor.whiskerLeft (CostructuredArrow.proj L c) β)).h) = _
  rw [← Category.assoc (prismEndpoint 0 _), prismEndpoint_zero_braiding,
    ← Category.assoc (SSet.ι₀), SSet.ι₀_comp, Category.assoc, SSet.Homotopy.h₀,
    ← Category.assoc, ← joinMap_comp, Category.id_comp, Iso.hom_inv_id,
    joinMap_id, Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories.F1B
