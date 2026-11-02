module

public import SerrePositivity.InfinityCategories.F1B.Cofinality.InitialTerminalWeakContractibility
public import SerrePositivity.InfinityCategories.Core.IdentityCocone

/-!
概要：指定頂点から出る coslice は弱可縮。
方針：恒等余錐の始対象性から弱可縮性を得る。
規約：coslice 自体の Kan 性は主張しない。
使われ方：Kerodon Theorem 7.2.3.1 の必要性。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：quasicategory の頂点から出る coslice は弱可縮。
方針：恒等余錐が始対象であるという定理を弱可縮性へ渡す。
規約：底 X だけに quasicategory 性を要求する。
使われ方：Kerodon Proposition 4.7.3.20 と Corollary 4.7.3.23、Quillen A。 -/
lemma sliceUnder_isWeaklyContractible {X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌) :
    IsWeaklyContractible (sliceUnder (SSet.yonedaEquiv.symm x)) :=
  (cosliceIdentityCone_isInitialVertex x).isWeaklyContractible

end SerrePositivity.InfinityCategories
