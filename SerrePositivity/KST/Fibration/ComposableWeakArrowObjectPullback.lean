module
public import SerrePositivity.KST.Fibration.ComposableWeakArrowSPullback
public import SerrePositivity.KST.SConstruction.ObjectSConstruction

/-! # 接続した二つの W 辺の元の object S の厳密な引き戻し

全 gapped S_n の引き戻しを零単体で評価し、単体作用素を含む普遍性へ束ねる。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の二つの W 辺と共有端点の object S 図式は厳密引き戻し。 -/
theorem composableWeakArrow_objectS_isPullback {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsPullback (objectSConstructionFunctor.map (composableWeakFirstExact q))
      (objectSConstructionFunctor.map (composableWeakNextExact q))
      (objectSConstructionFunctor.map (weakArrowTargetDiagram q))
      (objectSConstructionFunctor.map (weakArrowSourceDiagram q)) := by
  apply IsPullback.of_forall_isPullback_app
  intro n
  exact (composableWeakArrow_sConstruction_isPullback q n.unop.len).map
    ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌))

end SerrePositivity.KST.Fibration
