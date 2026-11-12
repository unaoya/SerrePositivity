module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeLeg

/-!
概要：通常の錐と native な錐の比較の自然性。
方針：点側の制限と脚の公式から join 上の射の外延性を使う。
規約：元の添字の制限と標的への後合成を厳密に比較する。
使われ方：B5 の右 Kan の標準錐の同定。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：nerve へ移した錐の点側の制限は元の頂点包含に等しい。
方針：join の両境界と全ての脚の一次単体を比較する。
規約：元の指定関手と錐を保つ厳密な等式。
使われ方：B5 の右 Kan の局所錐の古典比較。 -/
lemma nerveCone_point {I C : Type u} [Category.{u} I] [Category.{u} C]
    {F : I ⥤ C} (c : Cone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (nerve I) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c).val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c.pt := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (nerve I) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveMap I ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor c)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_initialJoinNerveMap]
  rfl

/-- 概要：join の脚の単体は通常の関手による添字変更と可換。
方針：join の両境界と全ての脚の一次単体を比較する。
規約：元の指定関手と錐を保つ厳密な等式。
使われ方：B5 の右 Kan の局所錐の古典比較。 -/
lemma coneLegSimplex_natural {J I : Type u} [Category.{u} J] [Category.{u} I]
    (H : J ⥤ I) (i : J) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap H)).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneLegSimplex i) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneLegSimplex (H.obj i) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum (n := 1) (l := 1) (r := 1) rfl
    (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) ((nerveMap H).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) = _
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.mkOfSum (n := 1) (l := 1) (r := 1) rfl
    (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))
      ((nerveMap H).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ i)) = _
  rw [nerveMap_app_mk₀]
  rfl

/-- 概要：nerve の錐の比較は通常の錐の制限と可換。
方針：join の両境界と全ての脚の一次単体を比較する。
規約：元の指定関手と錐を保つ厳密な等式。
使われ方：B5 の右 Kan の局所錐の古典比較。 -/
lemma nerveCone_whisker {J I C : Type u} [Category.{u} J] [Category.{u} I] [Category.{u} C]
    {F : I ⥤ C} (c : Cone F) (H : J ⥤ I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap H) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (c.whisker H)).val := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerve_joinPoint_hom_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp, nerveCone_point, nerveCone_point]
    rfl
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c).property, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (c.whisker H)).property]
    rfl
  · intro i
    rw [NatTrans.comp_app_apply, coneLegSimplex_natural, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_leg, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_leg]
    rfl

/-- 概要：nerve の錐の比較は通常の関手による像と可換。
方針：join の両境界と全ての脚の一次単体を比較する。
規約：元の指定関手と錐を保つ厳密な等式。
使われ方：B5 の右 Kan の局所錐の古典比較。 -/
lemma nerveCone_mapCone {I C D : Type u} [Category.{u} I] [Category.{u} C] [Category.{u} D]
    {F : I ⥤ C} (c : Cone F) (H : C ⥤ D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c).val ≫ nerveMap H = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (H.mapCone c)).val := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerve_joinPoint_hom_ext
  · rw [← Category.assoc, nerveCone_point, nerveCone_point]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    change (nerveMap H).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ c.pt) =
      ComposableArrows.mk₀ (H.obj c.pt)
    exact nerveMap_app_mk₀ H c.pt
  · rw [← Category.assoc, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c).property,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (H.mapCone c)).property]
    rfl
  · intro i
    rw [NatTrans.comp_app_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_leg, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_leg, nerveMap_app_mk₁]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
