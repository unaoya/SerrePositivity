module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentAdjacent

/-!
# 元の三列の区間合成と同じ三つの射の合成

概要：元の三つの forward 列の区間合成が元の同じ三つの隣接射の合成であることを証明する。
方針：元の区間を二度分割し、各一列の回収を使う。
規約：端点の移送を含む元の Segment.map を使う。
使われ方：三列 collapse の元の列への回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {X Y : C}
  (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.word X Y)

lemma segment_composite :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S (0 : Fin 4) (Fin.last 3) (by decide)
      (fun i _ _ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.direction i) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward S (0 : Fin 3) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.direction 0) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward S (1 : Fin 3) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.direction 1) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward S (2 : Fin 3) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.direction 2) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision.map_comp .forward S (0 : Fin 4) (1 : Fin 4) (Fin.last 3) (by decide) (by decide)]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision.map_comp .forward S (1 : Fin 4) (2 : Fin 4) (Fin.last 3) (by decide) (by decide)]
  have h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S (0 : Fin 4) (1 : Fin 4) (by decide)
      (fun i _ _ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.direction i) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward S (0 : Fin 3) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.direction 0) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .forward S (0 : Fin 3) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.direction 0)
  have h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S (1 : Fin 4) (2 : Fin 4) (by decide)
      (fun i _ _ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.direction i) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward S (1 : Fin 3) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.direction 1) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .forward S (1 : Fin 3) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.direction 1)
  have h2 : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S (2 : Fin 4) (Fin.last 3) (by decide)
      (fun i _ _ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.direction i) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward S (2 : Fin 3) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.direction 2) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .forward S (2 : Fin 3) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.direction 2)
  rw [h0, h1, h2]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
