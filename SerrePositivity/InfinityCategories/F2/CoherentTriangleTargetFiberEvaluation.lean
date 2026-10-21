module

public import SerrePositivity.InfinityCategories.F2.PointedSectionTargetFiber
public import SerrePositivity.InfinityCategories.F2.CoherentTriangleDiagramEndpoints
public import SerrePositivity.InfinityCategories.F2.PointedTriangleDiagramTarget

/-!
概要：局所三角形の終点評価を、実際の元の二つの小さい fiber 射の合成へ同定する。
方針：最後の頂点の等式を明示し、同じ fiber の包含で射を比較して元の宇宙へ戻す。
規約：指定した端点を保持。使われ方：左右の全三角形比較の共通終点への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)
local notation "H" => coherentSmallFiberPointedTriangle F G J x y T b
variable (D : (Δ[2] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
  (hD : D = coherentTransformationPointDiagram T.diagram (ULift.up b))

include hD in
/-- 三角形の別表示でも終点は元の同じ最後の空間値。 -/
lemma coherentTriangleTargetFiber_vertex :
    (stdSimplex.δ (0 : Fin 3) ≫ D).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 1) = J.app (Opposite.op ⦋0⦌) (ULift.up b) := by
  rw [hD]
  exact coherentTriangleDiagram_target_vertex T (ULift.up b)

/-- 図式側の辺の切断を、元の最後の小さい fiber へ戻す終点評価。 -/
def coherentTriangleTargetFiberEvaluation :
    relativeFunctorSpace pointedSpaceProjection (stdSimplex.δ (0 : Fin 3) ≫ D) ⟶
      coherentNativeTriangleFiberParameters J b :=
  pointedSectionTargetFiber J b (stdSimplex.δ (0 : Fin 3) ≫ D)
    (coherentTriangleTargetFiber_vertex F G J x y T b D hD)

/-- 同じ元の局所全三角形を終点で評価すると、元の実際の二 fiber 射の合成になる。 -/
lemma coherentTriangleTargetFiberEvaluation_eq
    (hH : H ≫ pointedSpaceProjection = fst Δ[2] (coherentNativeTriangleFiberParameters F b) ≫ D) :
    pointedTriangleFaceSections D H hH 0 ≫
        coherentTriangleTargetFiberEvaluation F G J x y T b D hD =
      (SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberMap (smallLeftUnstraighteningProjection F)
          (smallLeftUnstraighteningProjection G) (coherentTransformationTotalMap F G x)
          (coherentTransformationTotalMap_projection F G x) b ≫
        vertexFiberMap (smallLeftUnstraighteningProjection G)
          (smallLeftUnstraighteningProjection J) (coherentTransformationTotalMap G J y)
          (coherentTransformationTotalMap_projection G J y) b) := by
  subst D
  apply pointedSectionTargetFiber_eq_of_evaluate_ι
  exact coherentSmallFiberTriangleDiagramTarget_evaluate_ι F G J x y T b

/-- 同じ元の最後の fiber への終点評価は Kan fibration。 -/
lemma coherentTriangleTargetFiberEvaluation_fibration :
    Fibration (coherentTriangleTargetFiberEvaluation F G J x y T b D hD) :=
  pointedSectionTargetFiber_fibration J b _ _

end SerrePositivity.InfinityCategories.F2
