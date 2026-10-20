module

public import SerrePositivity.InfinityCategories.F1.PointedRightFiberComparison

/-!
概要：右区間評価を元の coslice fiber の区間族へ制限すると、元の点の族を回収する。
方針：一点 coslice 全体の恒等射の同じ輸送比較を、全 fiber 上の関手同型として保つ。
規約：同値性の命題だけに弱めず、実際の射と恒等射の比較を使う。
使われ方：右 Hom の係数比較の零単体を、指定した実際の pointed 点へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の coslice fiber の区間族で評価すると、同じ fiber 全体上で恒等射と同型。 -/
def pointedRightIntervalEvaluate_cosliceIso (s : SpaceInfinity.{u} _⦋0⦌) :
    FunctorIso
      (cosliceFiberToIntervalMappingSpace pointSpaceVertex s ≫ pointedRightIntervalEvaluate s)
      (𝟙 (vertexFiber pointedSpaceProjection s)) := by
  have e := leftFibrationCosliceMap_transportIso pointedSpaceProjection
    pointSpaceVertex (cosliceIdentityCone pointSpaceVertex)
    (cosliceIdentityCone_projection pointSpaceVertex) (𝟙 _)
    (Category.id_comp pointedSpaceProjection) (by rfl) s
  change FunctorIso
    (vertexFiberMap pointedSpaceProjection pointedSpaceProjection (𝟙 PointedSpaceInfinity.{u})
      (Category.id_comp pointedSpaceProjection) s)
    (diagonalFiberTransport pointedSpaceProjection (SSet.const pointedSpaceIdentityPoint)
      (cosliceFiberToIntervalMappingSpace pointSpaceVertex s)) at e
  rw [vertexFiberMap_id] at e
  have h : cosliceFiberToIntervalMappingSpace pointSpaceVertex s ≫
      pointedRightIntervalEvaluate s =
      diagonalFiberTransport pointedSpaceProjection (SSet.const pointedSpaceIdentityPoint)
        (cosliceFiberToIntervalMappingSpace pointSpaceVertex s) := by
    rw [pointedRightIntervalEvaluate, diagonalFiberTransport_precomp,
      SSet.comp_const, Category.comp_id]
  rw [h]
  exact e.symm

end SerrePositivity.InfinityCategories
