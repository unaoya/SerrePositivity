module

public import SerrePositivity.InfinityCategories.F1.Joins.CosliceTwistedArrowTarget
public import SerrePositivity.InfinityCategories.F1B.Cofinality.QuillenASliceOpposite

/-!
概要：元の表現可能 right fibration の反転から、実際の終点固定の twisted arrow への比較。
方針：既存の底上の slice 反転同型を、coslice の錐の比較に合成する。
規約：元の sliceOverProjection の反転を始域に固定し、射影の一致と単射性を保つ。
使われ方：Yoneda の実際の対象図式と、元の表現可能 right fibration の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の表現可能 right fibration の反転からの、終点固定の twisted arrow への比較射。 -/
def rightRepresentableTwistedArrowMap {C : SSet.{u}} (c : C _⦋0⦌) :
    (sliceOver (SSet.yonedaEquiv.symm c)).op ⟶ twistedArrowTarget c :=
  (cofinalPointSliceOverOpIso c).hom.left ≫ cosliceToTwistedArrowTarget c

/-- 比較射は、元の表現可能 right fibration の射影の反転と厳密に可換。 -/
lemma rightRepresentableTwistedArrowMap_projection {C : SSet.{u}} (c : C _⦋0⦌) :
    rightRepresentableTwistedArrowMap c ≫ twistedArrowTargetProjection c =
      SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm c)) := by
  rw [rightRepresentableTwistedArrowMap, Category.assoc, cosliceToTwistedArrowTarget_projection]
  exact (cofinalPointSliceOverOpIso c).hom.w

/-- 元の表現可能 right fibration の反転からの比較は単射。 -/
instance rightRepresentableTwistedArrowMap_mono {C : SSet.{u}} (c : C _⦋0⦌) :
    Mono (rightRepresentableTwistedArrowMap c) := by
  have : IsIso (cofinalPointSliceOverOpIso c).hom.left :=
    inferInstanceAs (IsIso (((Over.forget C.op).mapIso (cofinalPointSliceOverOpIso c)).hom))
  unfold rightRepresentableTwistedArrowMap
  infer_instance

/-- 射影を保持する比較を、元の反転した底上の射としてまとめる。 -/
def rightRepresentableTwistedArrowComparison {C : SSet.{u}} (c : C _⦋0⦌) :
    Over.mk (SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm c))) ⟶
      Over.mk (twistedArrowTargetProjection c) :=
  Over.homMk (rightRepresentableTwistedArrowMap c) (rightRepresentableTwistedArrowMap_projection c)

end SerrePositivity.InfinityCategories
