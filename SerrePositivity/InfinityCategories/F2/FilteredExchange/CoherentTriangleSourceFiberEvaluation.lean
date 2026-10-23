module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedSectionSourceFiber
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTriangleDiagramEndpoints
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedTriangleDiagramSource

/-!
概要：局所三角形の図式側の始点評価を、実際の小さい第一 fiber 射へ厳密に同定する。
方針：端点の頂点等式を明示し、同じ fiber の包含で射を比較して縮小同型を消去する。
規約：fiber の同型を使って射を比較する。使われ方：native 比較の二脚の fiber 内での照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
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

local instance : KanComplex (vertexFiber (smallLeftUnstraighteningProjection G) b) :=
  vertexFiber_kanComplex_of_leftFibration _ _

include hD in
/-- 三角形の別表示でも、図式側の始点は元の同じ中間値である。 -/
lemma coherentTriangleSourceFiber_vertex :
    (stdSimplex.δ (0 : Fin 3) ≫ D).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 0) = G.app (Opposite.op ⦋0⦌) (ULift.up b) := by
  rw [hD]
  exact coherentTriangleDiagram_source_vertex T (ULift.up b)

/-- 元の三角形の図式側の辺の切断から、中間の実際の小さい fiber へ戻す写像。 -/
def coherentTriangleSourceFiberEvaluation :
    relativeFunctorSpace pointedSpaceProjection (stdSimplex.δ (0 : Fin 3) ≫ D) ⟶
      coherentNativeTriangleFiberParameters G b :=
  pointedSectionSourceFiber G b (stdSimplex.δ (0 : Fin 3) ≫ D)
    (coherentTriangleSourceFiber_vertex F G J x y T b D hD)

/-- 同じ元の全局所三角形の切断を評価すると、元の実際の第一 fiber 射になる。 -/
lemma coherentTriangleSourceFiberEvaluation_eq
    (hH : H ≫ pointedSpaceProjection = fst Δ[2] (coherentNativeTriangleFiberParameters F b) ≫ D) :
    pointedTriangleFaceSections D H hH 0 ≫
        coherentTriangleSourceFiberEvaluation F G J x y T b D hD =
      (SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberMap (smallLeftUnstraighteningProjection F)
          (smallLeftUnstraighteningProjection G) (coherentTransformationTotalMap F G x)
          (coherentTransformationTotalMap_projection F G x) b) := by
  subst D
  apply pointedSectionSourceFiber_eq_of_evaluate_ι
  exact coherentSmallFiberTriangleDiagramSource_evaluate_ι F G J x y T b

/-- 辺の切断から実際の元の fiber へ戻す同じ写像は同値。 -/
lemma coherentTriangleSourceFiberEvaluation_isQCatEquivalence :
    IsQCatEquivalence (coherentTriangleSourceFiberEvaluation F G J x y T b D hD) :=
  pointedSectionSourceFiber_isQCatEquivalence G b _ _

end SerrePositivity.InfinityCategories.F2
