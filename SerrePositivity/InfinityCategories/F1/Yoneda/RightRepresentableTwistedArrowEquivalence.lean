module

public import SerrePositivity.InfinityCategories.F1.Yoneda.RightRepresentableTwistedArrowFiberComparison
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceTwistedHomEquivalence
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInfinityEquivalence

/-!
概要：元の表現可能 right fibration の反転から終点固定の twisted arrow への比較は同値。
方針：実際の fiber 写像を coslice 主比較に戻し、left fibration の fiber 判定を使う。
規約：構成済みの rightRepresentableTwistedArrowMap そのものの同値性を証明する。
使われ方：同じ Yoneda 対象前層と元の表現可能 right fibration の同一視。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

local instance {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    Quasicategory (twistedArrowTarget y) :=
  quasicategory_of_innerFibration (twistedArrowTargetProjection y)

/-- 元の表現可能射影の比較は、全ての頂点 fiber で実際の同値を誘導する。 -/
lemma rightRepresentableTwistedArrowFiberMap_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :
    IsQCatEquivalence (rightRepresentableTwistedArrowFiberMap x y) :=
  (rightRepresentableTwistedArrowFiberMap_isQCatEquivalence_iff x y).mpr
    (cosliceTwistedHomMap_isQCatEquivalence _ _)

/-- 元の射影を保つ比較の全空間での前合成同値。 -/
lemma rightRepresentableTwistedArrowMap_isPrecompositionEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    IsPrecompositionEquivalence (rightRepresentableTwistedArrowMap y) := by
  apply isPrecompositionEquivalence_of_leftFibration_fibers
    (SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm y)))
    (twistedArrowTargetProjection y) (rightRepresentableTwistedArrowMap y)
    (rightRepresentableTwistedArrowMap_projection y)
  intro b
  obtain ⟨x, rfl⟩ := SSet.opObjEquiv.symm.surjective b
  have h := rightRepresentableTwistedArrowFiberMap_isQCatEquivalence x y
  have hL := (qCatEquivalenceOfIso
    (HomotopyLimits.oppositeVertexFiberIso
      (sliceOverProjection (SSet.yonedaEquiv.symm y)) x)).isQCatEquivalence
  have hR := (qCatEquivalenceOfIso (twistedArrowTargetFiberIso x y)).isQCatEquivalence
  exact hR.cancel_right (hL.cancel_left h)

/-- 元の表現可能 right fibration の反転と終点固定の twisted arrow の比較は同値。 -/
lemma rightRepresentableTwistedArrowMap_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    IsQCatEquivalence (rightRepresentableTwistedArrowMap y) := by
  exact (rightRepresentableTwistedArrowMap_isPrecompositionEquivalence y).isQCatEquivalence

/-- 同じ比較射を left fibrations の ∞ 圏内で可逆にする。 -/
def rightRepresentableTwistedArrowVertexIso
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    VertexIso
      (leftFibrationInfinityVertex
        (SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm y))))
      (leftFibrationInfinityVertex (twistedArrowTargetProjection y)) :=
  leftFibrationInfinityVertexIsoOfPrecompositionEquivalence _ _
    (rightRepresentableTwistedArrowMap y) (rightRepresentableTwistedArrowMap_projection y)
    (rightRepresentableTwistedArrowMap_isPrecompositionEquivalence y)

end SerrePositivity.InfinityCategories
