module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenANecessary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.RightFibrationInitialFiber
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.WeakContractibleKan

/-!
概要：right fibration に対する Quillen A の十分性。
方針：底の coslice の始対象上の fiber と全空間を比較し、元の頂点 fiber に戻す。
規約：弱可縮性から全境界充填へ移すのは Kan 性が判明した頂点 fiber の中だけ。
使われ方：一般の射を right fibration に分解した後の判定。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：right fibration の coslice 引き戻しが弱可縮なら元の対応する頂点 fiber も弱可縮。
方針：coslice の恒等錐が始対象であることを使い、その上の fiber を同定する。
規約：底 B だけに quasicategory 性を要求する。
使われ方：Quillen A の弱可縮な coslice の条件を Kan fiber の条件へ移す。 -/
lemma rightFibration_vertexFiber_isWeaklyContractible_of_coslices
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p]
    (hc : ∀ b : B _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b))))
    (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b)
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (pullback.snd p q) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.pullback_snd p q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := p))⟩
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.rightFibration_initialFiber_isWeakHomotopyEquivalence
    (pullback.snd p q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_isInitialVertex b)
  have hF := hi.weaklyContractible_iff.mpr (hc b)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso p q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone b)
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne e.hom
    (MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions e.hom)).isWeakHomotopyEquivalence
  have h := he.weaklyContractible_iff.mp hF
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone b))) at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_projection] at h
  exact h

/-- 概要：right fibration の全ての coslice 引き戻しが弱可縮なら trivial Kan fibration。
方針：始点 fiber の比較と Kan fiber の弱可縮性判定を順に使う。
規約：元の coslice 引き戻しには Kan 性を要求しない。
使われ方：Quillen A の right 側の十分性の fibration の場合。 -/
lemma rightFibration_trivialKanFibration_of_weaklyContractible_coslices
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p]
    (hc : ∀ b : B _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.rightFibration_trivialKanFibration_of_weaklyContractible_fibers p
    (rightFibration_vertexFiber_isWeaklyContractible_of_coslices p hc)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
