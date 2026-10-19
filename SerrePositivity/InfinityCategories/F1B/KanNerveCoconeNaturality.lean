module

public import SerrePositivity.InfinityCategories.F1B.KanNerveCoconeExt

/-!
概要：通常の余錐と native な余錐の比較の自然性を構成する。
方針：join の両境界と脚の一次単体を照合する。
規約：元の図式・頂点・指定脚を保つ厳密な等式。
使われ方：B5 の左 Kan の標準余錐と指定輸送の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B


/-- 概要：余錐の nerve の表示は通常の添字の制限と可換。
方針：余錐の境界と全ての脚を比較する。
規約：同じ宇宙の小さい圏の指定図式を扱う。
使われ方：B5 の指定局所余錐の古典比較。 -/
lemma kanNerveCocone_whisker {J I C : Type u} [Category.{u} J] [Category.{u} I] [Category.{u} C]
    {F : I ⥤ C} (c : Cocone F) (H : J ⥤ I) :
    joinMap (nerveMap H) (𝟙 (Δ[0] : SSet.{u})) ≫ (kanNerveCoconeEquiv c).val =
      (kanNerveCoconeEquiv (c.whisker H)).val := by
  apply kanNerve_joinTerminal_hom_ext
  · rw [← Category.assoc, joinInl_joinMap, Category.assoc,
      (kanNerveCoconeEquiv c).property, (kanNerveCoconeEquiv (c.whisker H)).property]
    rfl
  · rw [← Category.assoc, joinInr_joinMap, Category.id_comp,
      kanNerveCocone_point, kanNerveCocone_point]
    rfl
  · intro i
    rw [NatTrans.comp_app_apply, kanJoinCoconeLegSimplex_natural]
    change (kanNerveCoconeEquiv c).val.app _
      (kanJoinCoconeLegSimplex ((nerveMap H).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ i))) = _
    rw [nerveMap_app_mk₀]
    change (kanNerveCoconeEquiv c).val.app (Opposite.op ⦋1⦌)
      (kanJoinCoconeLegSimplex (nerveVertex (H.obj i))) =
        (kanNerveCoconeEquiv (c.whisker H)).val.app (Opposite.op ⦋1⦌)
          (kanJoinCoconeLegSimplex (nerveVertex i))
    rw [kanNerveCocone_leg, kanNerveCocone_leg]
    rfl

/-- 概要：余錐の nerve の表示は通常の関手による像と可換。
方針：余錐の境界と全ての脚を比較する。
規約：同じ宇宙の小さい圏の指定図式を扱う。
使われ方：B5 の指定局所余錐の古典比較。 -/
lemma kanNerveCocone_mapCocone {I C D : Type u} [Category.{u} I] [Category.{u} C] [Category.{u} D]
    {F : I ⥤ C} (c : Cocone F) (H : C ⥤ D) :
    (kanNerveCoconeEquiv c).val ≫ nerveMap H = (kanNerveCoconeEquiv (H.mapCocone c)).val := by
  apply kanNerve_joinTerminal_hom_ext
  · rw [← Category.assoc, (kanNerveCoconeEquiv c).property,
      (kanNerveCoconeEquiv (H.mapCocone c)).property]
    rfl
  · rw [← Category.assoc, kanNerveCocone_point, kanNerveCocone_point]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    change (nerveMap H).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ c.pt) =
      ComposableArrows.mk₀ (H.obj c.pt)
    exact nerveMap_app_mk₀ H c.pt
  · intro i
    rw [NatTrans.comp_app_apply, kanNerveCocone_leg, kanNerveCocone_leg, nerveMap_app_mk₁]
    rfl

end SerrePositivity.InfinityCategories.F1B
