module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTwistedArrowTarget
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenASliceOpposite

/-!
概要：元の表現可能 right fibration の反転から、実際の終点固定の twisted arrow への比較。
方針：既存の底上の slice 反転同型を、coslice の錐の比較に合成する。
規約：元の sliceOverProjection の反転を始域に固定し、射影の一致と単射性を保つ。
使われ方：Yoneda の実際の対象図式と、元の表現可能 right fibration の照合。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 元の表現可能 right fibration の反転からの、終点固定の twisted arrow への比較射。 -/
def rightRepresentableTwistedArrowMap {C : SSet.{u}} (c : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm c)).op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowTarget c :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso c).hom.left ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceToTwistedArrowTarget c

/-- 比較射は、元の表現可能 right fibration の射影の反転と厳密に可換。 -/
lemma rightRepresentableTwistedArrowMap_projection {C : SSet.{u}} (c : C _⦋0⦌) :
    rightRepresentableTwistedArrowMap c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowTargetProjection c =
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c)) := by
  rw [rightRepresentableTwistedArrowMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceToTwistedArrowTarget_projection]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso c).hom.w

/-- 元の表現可能 right fibration の反転からの比較は単射。 -/
instance rightRepresentableTwistedArrowMap_mono {C : SSet.{u}} (c : C _⦋0⦌) :
    Mono (rightRepresentableTwistedArrowMap c) := by
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso c).hom.left :=
    inferInstanceAs (IsIso (((Over.forget C.op).mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso c)).hom))
  unfold rightRepresentableTwistedArrowMap
  infer_instance

/-- 射影を保持する比較を、元の反転した底上の射としてまとめる。 -/
def rightRepresentableTwistedArrowComparison {C : SSet.{u}} (c : C _⦋0⦌) :
    Over.mk (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c))) ⟶
      Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowTargetProjection c) :=
  Over.homMk (rightRepresentableTwistedArrowMap c) (rightRepresentableTwistedArrowMap_projection c)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
