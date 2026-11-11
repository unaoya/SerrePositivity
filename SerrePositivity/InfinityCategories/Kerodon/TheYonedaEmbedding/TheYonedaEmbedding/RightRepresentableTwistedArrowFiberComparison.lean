module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RightRepresentableTwistedArrowComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.CosliceTwistedHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.HomSwap
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TargetFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointSlicePrismReverse

/-!
概要：元の表現可能射影の比較の実際の fiber 写像を、coslice の両端固定の主比較へ戻す。
方針：右 slice の反転、pullback の fiber、両端交換の三つの厳密な同型を照合する。
規約：独立な写像空間同値で置き換えず、構成済みの比較射そのものについて述べる。
使われ方：残る主比較の同値性から元の表現可能射影の比較の同値性へ進む。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 終点固定の全空間への比較は、第一射影後に元の錐の反転比較を回収する。 -/
lemma rightRepresentableTwistedArrowMap_fst {C : SSet.{u}} (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.rightRepresentableTwistedArrowMap y ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowTargetInclusion y) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso y).hom.left ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceTwistedArrowMap (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.twistedArrowOppositeSwap C := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.rightRepresentableTwistedArrowMap, Category.assoc]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso y).hom.left ≫
    (pullback.lift _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceOppositeTwistedArrowMap_over y) ≫ _) = _
  rw [pullback.lift_fst]
  rfl

/-- 元の表現可能射影の比較を、右 slice fiber の反転と元の twisted arrow Hom の間で表す。 -/
def rightRepresentableTwistedArrowFiberMap {C : SSet.{u}} (x y : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y)) x).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace x y :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeVertexFiberIso _ x).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.rightRepresentableTwistedArrowMap y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.rightRepresentableTwistedArrowMap_projection y) (SSet.opObjEquiv.symm x) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowTargetFiberIso x y).hom

/-- 実際の fiber 写像は、元の coslice の主比較を厳密な同型で挟んだもの。 -/
lemma rightRepresentableTwistedArrowFiberMap_compare {C : SSet.{u}} (x y : C _⦋0⦌) :
    rightRepresentableTwistedArrowFiberMap x y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointSliceReverseFiberIso y x).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSwapIso x y).hom := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (SSet.opObjEquiv.symm x, y)
  rw [rightRepresentableTwistedArrowFiberMap, Category.assoc, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowTargetFiberIso_ι]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ _ _ _), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
  rw [Category.assoc, rightRepresentableTwistedArrowMap_fst]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeVertexFiberIso _ x).hom,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeVertexFiberIso_hom_ι]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSwapIso_ι]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap _ _), _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap_ι]
  simp only [← Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointSliceReverseFiberIso_ι]

/-- 実際の fiber 比較の同値性は、同じ coslice の主比較の同値性と厳密に同値。 -/
lemma rightRepresentableTwistedArrowFiberMap_isQCatEquivalence_iff
    {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (rightRepresentableTwistedArrowFiberMap x y) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)) := by
  rw [rightRepresentableTwistedArrowFiberMap_compare]
  have hL := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointSliceReverseFiberIso y x)).isQCatEquivalence
  have hR := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSwapIso x y)).isQCatEquivalence
  exact ⟨fun h ↦ hR.cancel_right (hL.cancel_left h), fun h ↦ hL.comp (h.comp hR)⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
