module

public import SerrePositivity.InfinityCategories.F1.RightRepresentableTwistedArrowComparison
public import SerrePositivity.InfinityCategories.F1.CosliceTwistedHomComparison
public import SerrePositivity.InfinityCategories.F1.TwistedArrowHomSwap
public import SerrePositivity.InfinityCategories.F1.TwistedArrowTargetFiber
public import SerrePositivity.InfinityCategories.F1.PointSlicePrismReverse

/-!
概要：元の表現可能射影の比較の実際の fiber 写像を、coslice の両端固定の主比較へ戻す。
方針：右 slice の反転、pullback の fiber、両端交換の三つの厳密な同型を照合する。
規約：独立な写像空間同値で置き換えず、構成済みの比較射そのものについて述べる。
使われ方：残る主比較の同値性から元の表現可能射影の比較の同値性へ進む。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 終点固定の全空間への比較は、第一射影後に元の錐の反転比較を回収する。 -/
lemma rightRepresentableTwistedArrowMap_fst {C : SSet.{u}} (y : C _⦋0⦌) :
    rightRepresentableTwistedArrowMap y ≫
      pullback.fst (twistedArrowProjection C) (twistedArrowTargetInclusion y) =
    (cofinalPointSliceOverOpIso y).hom.left ≫
      cosliceTwistedArrowMap (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y)) ≫
        twistedArrowOppositeSwap C := by
  rw [rightRepresentableTwistedArrowMap, Category.assoc]
  change (cofinalPointSliceOverOpIso y).hom.left ≫
    (pullback.lift _ _ (cosliceOppositeTwistedArrowMap_over y) ≫ _) = _
  rw [pullback.lift_fst]
  rfl

/-- 元の表現可能射影の比較を、右 slice fiber の反転と元の twisted arrow Hom の間で表す。 -/
def rightRepresentableTwistedArrowFiberMap {C : SSet.{u}} (x y : C _⦋0⦌) :
    (vertexFiber (sliceOverProjection (SSet.yonedaEquiv.symm y)) x).op ⟶
      twistedArrowHomSpace x y :=
  (HomotopyLimits.oppositeVertexFiberIso _ x).hom ≫
    vertexFiberMap _ _ (rightRepresentableTwistedArrowMap y)
      (rightRepresentableTwistedArrowMap_projection y) (SSet.opObjEquiv.symm x) ≫
        (twistedArrowTargetFiberIso x y).hom

/-- 実際の fiber 写像は、元の coslice の主比較を厳密な同型で挟んだもの。 -/
lemma rightRepresentableTwistedArrowFiberMap_compare {C : SSet.{u}} (x y : C _⦋0⦌) :
    rightRepresentableTwistedArrowFiberMap x y =
      (pointSliceReverseFiberIso y x).hom ≫
        cosliceTwistedHomMap (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x) ≫
          (twistedArrowHomSwapIso x y).hom := by
  apply vertexFiber_hom_ext (twistedArrowProjection C) (SSet.opObjEquiv.symm x, y)
  rw [rightRepresentableTwistedArrowFiberMap, Category.assoc, Category.assoc,
    twistedArrowTargetFiberIso_ι]
  rw [← Category.assoc (vertexFiberMap _ _ _ _ _), vertexFiberMap_ι]
  rw [Category.assoc, rightRepresentableTwistedArrowMap_fst]
  rw [← Category.assoc (HomotopyLimits.oppositeVertexFiberIso _ x).hom,
    HomotopyLimits.oppositeVertexFiberIso_hom_ι]
  simp only [Category.assoc]
  rw [twistedArrowHomSwapIso_ι]
  rw [← Category.assoc (cosliceTwistedHomMap _ _), cosliceTwistedHomMap_ι]
  simp only [← Category.assoc]
  rw [pointSliceReverseFiberIso_ι]

/-- 実際の fiber 比較の同値性は、同じ coslice の主比較の同値性と厳密に同値。 -/
lemma rightRepresentableTwistedArrowFiberMap_isQCatEquivalence_iff
    {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :
    IsQCatEquivalence (rightRepresentableTwistedArrowFiberMap x y) ↔
      IsQCatEquivalence
        (cosliceTwistedHomMap (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)) := by
  rw [rightRepresentableTwistedArrowFiberMap_compare]
  have hL := (qCatEquivalenceOfIso (pointSliceReverseFiberIso y x)).isQCatEquivalence
  have hR := (qCatEquivalenceOfIso (twistedArrowHomSwapIso x y)).isQCatEquivalence
  exact ⟨fun h ↦ hR.cancel_right (hL.cancel_left h), fun h ↦ hL.comp (h.comp hR)⟩

end SerrePositivity.InfinityCategories
