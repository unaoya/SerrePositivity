module

public import SerrePositivity.KST.Spectra.CofibrantSequenceLifting
public import SerrePositivity.KST.Spectra.CircleMappingComponents

/-!
概要：通常の円の loop への射を Kan 円の loop への射に持ち上げる。
方針：円の anodyne 置換による源の制限の全単射 RLP を使う。
規約：持ち上げの選択に厳密な自然性を主張しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。Ω スペクトルの随伴構造射を Kan 円で比較する。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：通常の円の loop への点つき射を Kan 円の loop へ持ち上げる。
方針：源の基点包含と円の anodyne な制限の RLP で点つき持ち上げを選ぶ。
規約：標的の基礎対象 Z は Kan。
使われ方：BF 1978 §2、HA §1.4.2。各段の随伴構造射の Kan 円での実現。 -/
def kanLoopLift {Y Z : PointedSimplicialSet.{u}} [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z) :
    Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z :=
  (pointedMapLift (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} Z)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp CirclePower.unit
      (PointedKanReplacement.unit_anodyne PointedSimplicialSet.circle.{u}) Z) a).val

/-- 概要：持ち上げを通常の円へ制限すると元の loop への射となる。
方針：点つき持ち上げの可換式を取り出す。
規約：点つき射の厳密な等式。
使われ方：Goerss–Jardine I §7。二つの loop 模型の比較の可換式。 -/
@[reassoc]
theorem kanLoopLift_comparison {Y Z : PointedSimplicialSet.{u}} [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z) :
    kanLoopLift a ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} Z = a :=
  (pointedMapLift (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} Z)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp CirclePower.unit
      (PointedKanReplacement.unit_anodyne PointedSimplicialSet.circle.{u}) Z) a).property

/-- 概要：元の loop への射が全基点 π_* 同型なら Kan 円への持ち上げも同型。
方針：円の制限の同型性を比較の可換式から打ち消す。
規約：源 Y も Kan とする。
使われ方：BF 1978 §2。Kan 円による Ω 条件の実現。 -/
theorem kanLoopLift_piIsomorphism {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (kanLoopLift a).right := by
  have hq : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} Z).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp CirclePower.unit
      (PointedKanReplacement.unit_anodyne PointedSimplicialSet.circle.{u}) Z)
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} Z).right)
    _ hq
  have h := congrArg Under.Hom.right (kanLoopLift_comparison a)
  change (kanLoopLift a).right ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} Z).right =
    a.right at h
  rw [h]
  exact ha

end

end SerrePositivity.KST.Spectra
