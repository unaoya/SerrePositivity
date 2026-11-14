module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.Pointed
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialJoinIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedInitial
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedRetraction
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridInitialPoint
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionInitialReplacementSquare
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PullbackConeVertex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ThinNerveMonomorphism

/-!
概要：比較格子の初期角を実引き戻しへ置換し、矢印圏の普遍性へ接続する。
方針：穿孔格子の同じ錐と全非初期単体を厳密に保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionFullInputCospanBoundary : (horn 2 2 : SSet.{u}) ⟶
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex.{u} :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanBoundary ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull.toFunctor

lemma excisionFullInputCospanBoundary_projection :
    excisionFullInputCospanBoundary.{u} ≫
      nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding := by
  unfold excisionFullInputCospanBoundary
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull_projection, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanBoundary_projection, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram_lowerLeft]
  simp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding, Category.assoc]

lemma excisionGridSquareEmbedding_initial :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding.{u} 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridInitialPoint := by
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionFullInputCospanBoundary_leftAnodyne :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions excisionFullInputCospanBoundary.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.comp_mem _ _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanBoundary_leftAnodyne
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedToFull_leftAnodyne

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
