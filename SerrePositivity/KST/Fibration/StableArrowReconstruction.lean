module
public import SerrePositivity.KST.Fibration.StableHomVertexRecovery
public import SerrePositivity.KST.Fibration.StableCoreSingleKanHom
public import SerrePositivity.InfinityCategories.F1.Coherent.EdgeEquiv

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
theorem stableArrowExactMap_reconstruct (a : StableInfinity.{u} _⦋1⦌) :
    (stableArrow (stableArrowExactMap a)).edge = a := by
  have he : stableArrowExactMap a = (coherentNerveArrowData a).2.2 := by
    change stableHomExactMap (coherentArrowHomVertex a) =
      (SimplicialCategory.homEquiv' _ _).symm (coherentArrowHomVertex a)
    apply (SimplicialCategory.homEquiv' (C := StableQCat.{u})
      (a.obj ⟨ULift.up 0⟩) (a.obj ⟨ULift.up 1⟩)).injective
    rw [stableHom_homEquiv'_ExactMap, Equiv.apply_symm_apply]
  change (coherentNerveEdge (stableArrowExactMap a)).edge = a
  rw [he]
  exact coherentNerveArrowData_reconstruct a

/-- 任意の指定安定辺の core S Kan 像も、同じ回収完全射の元の実射の辺に厳密一致する。 -/
theorem stableCoreSingleKan_edge_reconstruct (a : StableInfinity.{u} _⦋1⦌) :
    (coherentNerveMap stableCoreSingleKanEnrichedFunctor).app (Opposite.op ⦋1⦌) a =
      (coherentNerveEdge (stableCoreSingleKanMap (stableArrowExactMap a))).edge := by
  rw [← stableArrowExactMap_reconstruct a]
  exact stableCoreSingleKan_edge _

end SerrePositivity.KST.Fibration
