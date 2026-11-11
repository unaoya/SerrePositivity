module
public import SerrePositivity.KST.Fibration.StableHomVertexRecovery
public import SerrePositivity.KST.Fibration.StableCoreSingleKanHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.EdgeEquiv

/-!
概要：元の任意の安定 coherent 辺を、同じ回収完全射と実 core S Kan 射で厳密復元する。
方針：既存の coherent 射データの全単射と、同じ全 Hom の固定射比較を使う。
規約：元の辺と両端を保持し、ホモトピー類への弱化を行わない。
使われ方：指定 Verdier 上側二胞体の元の短辺を、三角柱の実入力へ読み戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 任意の元の安定 coherent 辺は、回収した同じ実完全射から厳密に復元される。 -/
theorem stableArrowExactMap_reconstruct (a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (stableArrowExactMap a)).edge = a := by
  have he : stableArrowExactMap a = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData a).2.2 := by
    change stableHomExactMap (coherentArrowHomVertex a) =
      (SimplicialCategory.homEquiv' _ _).symm (coherentArrowHomVertex a)
    apply (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
      (a.obj ⟨ULift.up 0⟩) (a.obj ⟨ULift.up 1⟩)).injective
    rw [stableHom_homEquiv'_ExactMap, Equiv.apply_symm_apply]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (stableArrowExactMap a)).edge = a
  rw [he]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_reconstruct a

/-- 任意の指定安定辺の core S Kan 像も、同じ回収完全射の元の実射の辺に厳密一致する。 -/
theorem stableCoreSingleKan_edge_reconstruct (a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app (Opposite.op ⦋1⦌) a =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (stableCoreSingleKanMap (stableArrowExactMap a))).edge := by
  rw [← stableArrowExactMap_reconstruct a]
  exact stableCoreSingleKan_edge _

end SerrePositivity.KST.Fibration
