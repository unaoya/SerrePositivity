module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedOppositeHomFixedAction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber

/-!
概要：全反転 Hom の作用族の固定射での頂点は元の後合成関手の頂点。
方針：零単体の Yoneda 射を定値射へ戻し、同じ実円柱を uncurry で検出する。
規約：元の固定射・全初点・標準 fiber 比較を保持する。
使われ方：反転精密化の作用の両端を実二辺合成・長辺の関手へ正規化する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 固定射における全反転 Hom 作用の頂点は同じ元の後合成関手の頂点。 -/
lemma pointedOppositeHomAction_vertex {K L : KanObject.{u}} (f : K ⟶ L) :
    (pointedOppositeHomAction K L).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm (SimplicialCategory.homEquiv' K L f))) =
    functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
      (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject f)) ≫
        pointedCoherentFiberComparison L) := by
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_comp]
  simp only [SSet.yonedaEquiv_symm_zero]
  apply uncurry_injective
  rw [pointedOppositeHomAction_fixed_uncurry, uncurry_const_functorVertex]

end SerrePositivity.InfinityCategories.F2
