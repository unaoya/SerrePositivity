module

public import SerrePositivity.InfinityCategories.F1B.KanNerveConeLeg

/-!
概要：通常の錐と native な錐の比較の自然性。
方針：点側の制限と脚の公式から join 上の射の外延性を使う。
規約：元の添字の制限と標的への後合成を厳密に比較する。
使われ方：B5 の右 Kan の標準錐の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：nerve へ移した錐の点側の制限は元の頂点包含に等しい。
方針：join の両境界と全ての脚の一次単体を比較する。
規約：元の指定関手と錐を保つ厳密な等式。
使われ方：B5 の右 Kan の局所錐の古典比較。 -/
lemma kanNerveCone_point {I C : Type u} [Category.{u} I] [Category.{u} C]
    {F : I ⥤ C} (c : Cone F) :
    joinInl (Δ[0] : SSet.{u}) (nerve I) ≫ (kanNerveCone c).val = nervePoint c.pt := by
  change joinInl (Δ[0] : SSet.{u}) (nerve I) ≫
    (HomotopyLimits.initialJoinNerveMap I ≫ nerveMap (kanConeWithInitialFunctor c)) = _
  rw [← Category.assoc, HomotopyLimits.joinInl_initialJoinNerveMap]
  rfl

/-- 概要：join の脚の単体は通常の関手による添字変更と可換。
方針：join の両境界と全ての脚の一次単体を比較する。
規約：元の指定関手と錐を保つ厳密な等式。
使われ方：B5 の右 Kan の局所錐の古典比較。 -/
lemma kanConeLegSimplex_natural {J I : Type u} [Category.{u} J] [Category.{u} I]
    (H : J ⥤ I) (i : J) :
    (joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap H)).app (Opposite.op ⦋1⦌)
      (kanConeLegSimplex i) = kanConeLegSimplex (H.obj i) := by
  change Join.mkOfSum (n := 1) (l := 1) (r := 1) rfl
    (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) ((nerveMap H).app (Opposite.op ⦋0⦌) (nerveVertex i)) = _
  change Join.mkOfSum (n := 1) (l := 1) (r := 1) rfl
    (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))
      ((nerveMap H).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ i)) = _
  rw [nerveMap_app_mk₀]
  rfl

/-- 概要：nerve の錐の比較は通常の錐の制限と可換。
方針：join の両境界と全ての脚の一次単体を比較する。
規約：元の指定関手と錐を保つ厳密な等式。
使われ方：B5 の右 Kan の局所錐の古典比較。 -/
lemma kanNerveCone_whisker {J I C : Type u} [Category.{u} J] [Category.{u} I] [Category.{u} C]
    {F : I ⥤ C} (c : Cone F) (H : J ⥤ I) :
    joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap H) ≫ (kanNerveCone c).val =
      (kanNerveCone (c.whisker H)).val := by
  apply kanNerve_joinPoint_hom_ext
  · rw [← Category.assoc, joinInl_joinMap, Category.id_comp, kanNerveCone_point, kanNerveCone_point]
    rfl
  · rw [← Category.assoc, joinInr_joinMap, Category.assoc,
      (kanNerveCone c).property, (kanNerveCone (c.whisker H)).property]
    rfl
  · intro i
    rw [NatTrans.comp_app_apply, kanConeLegSimplex_natural, kanNerveCone_leg, kanNerveCone_leg]
    rfl

/-- 概要：nerve の錐の比較は通常の関手による像と可換。
方針：join の両境界と全ての脚の一次単体を比較する。
規約：元の指定関手と錐を保つ厳密な等式。
使われ方：B5 の右 Kan の局所錐の古典比較。 -/
lemma kanNerveCone_mapCone {I C D : Type u} [Category.{u} I] [Category.{u} C] [Category.{u} D]
    {F : I ⥤ C} (c : Cone F) (H : C ⥤ D) :
    (kanNerveCone c).val ≫ nerveMap H = (kanNerveCone (H.mapCone c)).val := by
  apply kanNerve_joinPoint_hom_ext
  · rw [← Category.assoc, kanNerveCone_point, kanNerveCone_point]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    change (nerveMap H).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ c.pt) =
      ComposableArrows.mk₀ (H.obj c.pt)
    exact nerveMap_app_mk₀ H c.pt
  · rw [← Category.assoc, (kanNerveCone c).property,
      (kanNerveCone (H.mapCone c)).property]
    rfl
  · intro i
    rw [NatTrans.comp_app_apply, kanNerveCone_leg, kanNerveCone_leg, nerveMap_app_mk₁]
    rfl

end SerrePositivity.InfinityCategories.F1B
