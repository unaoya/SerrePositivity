module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CosliceFiberVertexFactor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedReverseFiberCoordinates
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointedCoherentFiberComparison

/-!
概要：反転 Kan の全一点 Hom 比較を、元の coherent 比較の同じ頂点移送へ戻す。
方針：係数の交換同型を消去し、二頂点変更を始点と終点に分ける。
規約：元の全係数を保持し逆同値を選ばない。使われ方：左右区間の全作用の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 同じ反転 fiber 比較の係数を戻すと、元の coherent 比較の終点表示変更となる。 -/
lemma pointedReverseKanFiberComparison_normalized (K : KanObject.{u}) :
    (uliftOppositeIso (SimplicialCategory.sHom pointKanObject K)).hom ≫
      pointedReverseKanFiberComparison K = pointedCoherentFiberComparison K ≫
        eqToHom (congrArg (vertexFiber pointedSpaceProjection)
          (spaceInfinityVertex_eq_coherent K).symm) := by
  rw [pointedReverseKanFiberComparison_coordinates]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [cosliceFiberVerticesIso_target_factor]
  rfl

end SerrePositivity.InfinityCategories.F2
