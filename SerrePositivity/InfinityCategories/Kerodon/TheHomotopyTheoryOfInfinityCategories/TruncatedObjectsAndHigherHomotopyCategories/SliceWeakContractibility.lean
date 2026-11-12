module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialTerminalWeakContractibility
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IdentityCocone

/-!
概要：指定頂点から出る coslice は弱可縮。
方針：恒等余錐の始対象性から弱可縮性を得る。
規約：coslice 自体の Kan 性は主張しない。
使われ方：Kerodon Theorem 7.2.3.1（Tag 02NY） の必要性。

対応節は Kerodon 4.7（Tag 05EA）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-- 概要：quasicategory の頂点から出る coslice は弱可縮。
方針：恒等余錐が始対象であるという定理を弱可縮性へ渡す。
規約：底 X だけに quasicategory 性を要求する。
使われ方：Kerodon Proposition 4.7.3.20（Tag 02J2） と Corollary 4.7.3.23、Quillen A。 -/
lemma sliceUnder_isWeaklyContractible {X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_isInitialVertex x).isWeaklyContractible

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
