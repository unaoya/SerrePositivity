module

public import SerrePositivity.InfinityCategories.F1.Yoneda.RightRepresentableTwistedArrowEquivalence
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaTargetBaseChange

/-!
概要：実際の Yoneda 写像の対象前層を、元の表現可能 right fibration の分類図式と同定する。
方針：同じ全空間の比較を分類写像で送り、既存の終点固定の底変換同型と合成する。
規約：対象ごとの別の Hom 前層を新しく選ばず、元の representablePresheafInfinity を使う。
使われ方：right fibration 版の Yoneda 評価を同じ Yoneda 写像へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の slice の分類図式から、同じ終点固定の twisted arrow の分類図式への同型。 -/
def rightRepresentableTwistedArrowDiagramIso
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    FunctorIso
      (leftStraighteningInfinityDiagram
        (SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm y))))
      (leftStraighteningInfinityDiagram (twistedArrowTargetProjection y)) := by
  have h := VertexIso.map (rightRepresentableTwistedArrowVertexIso y)
    (leftStraighteningInfinityMap C.op)
  rw [← leftStraighteningInfinityDiagram_vertex,
    ← leftStraighteningInfinityDiagram_vertex] at h
  exact h

/-- 実際の Yoneda 対象前層は、元の表現可能 right fibration の反転の分類図式。 -/
def representablePresheafInfinity_sliceIso
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    FunctorIso (representablePresheafInfinity y)
      (leftStraighteningInfinityDiagram
        (SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm y)))) :=
  representablePresheafInfinity_targetIso y ≪≫ (rightRepresentableTwistedArrowDiagramIso y).symm

end SerrePositivity.InfinityCategories
