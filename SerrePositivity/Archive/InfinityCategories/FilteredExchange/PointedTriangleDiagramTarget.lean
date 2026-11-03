module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedTriangleDiagramSource
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallFiberTriangleFinal

/-!
概要：図式側の辺の終点評価を、元の小さい二つの fiber 射の合成へ同定する。
方針：相対 curry の終点評価を展開し、同じ全三角形の最終頂点の式へ接続する。
規約：全族の厳密な包含式。使われ方：左右の指定比較の共通終点への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 図式側の辺の終点は、同じ全三角形の最後の頂点である。 -/
lemma pointedTriangleDiagramTarget_evaluate_ι {A : SSet.{u + 1}}
    (D : (Δ[2] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
    (W : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hW : W ≫ pointedSpaceProjection = fst Δ[2] A ≫ D) :
    pointedTriangleFaceSections D W hW 0 ≫
      relativeFunctorEvaluate pointedSpaceProjection (stdSimplex.δ (0 : Fin 3) ≫ D)
        (stdSimplex.obj₀Equiv.symm 1) ≫
      vertexFiberι pointedSpaceProjection
        ((stdSimplex.δ (0 : Fin 3) ≫ D).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm 1)) =
        prismEndpoint 1 A ≫ (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ W := by
  rw [pointedTriangleFaceSections, relativeCurry_evaluate_ι]
  rfl

variable {B : SSet.{u}}
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)
local notation "D" => coherentTransformationPointDiagram T.diagram (ULift.up b)
local notation "H" => coherentSmallFiberPointedTriangle F G J x y T b
local notation "hH" => coherentSmallFiberPointedTriangle_projection F G J x y T b
local notation "fx" => vertexFiberMap (smallLeftUnstraighteningProjection F)
  (smallLeftUnstraighteningProjection G) (coherentTransformationTotalMap F G x)
  (coherentTransformationTotalMap_projection F G x) b
local notation "fy" => vertexFiberMap (smallLeftUnstraighteningProjection G)
  (smallLeftUnstraighteningProjection J) (coherentTransformationTotalMap G J y)
  (coherentTransformationTotalMap_projection G J y) b

/-- 元の図式辺の終点評価は、実際の二つの小さい fiber 射の合成の pointed 表示。 -/
lemma coherentSmallFiberTriangleDiagramTarget_evaluate_ι :
    pointedTriangleFaceSections D H hH 0 ≫
      relativeFunctorEvaluate pointedSpaceProjection (stdSimplex.δ (0 : Fin 3) ≫ D)
        (stdSimplex.obj₀Equiv.symm 1) ≫
      vertexFiberι pointedSpaceProjection
        ((stdSimplex.δ (0 : Fin 3) ≫ D).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm 1)) =
      (SSet.uliftFunctor.{u + 1, u}).map (fx ≫ fy) ≫ coherentCospanFiberPointedSource J b :=
  (pointedTriangleDiagramTarget_evaluate_ι D H hH).trans
    (coherentSmallFiberPointedTriangle_final_fiber F G J x y T b)

end SerrePositivity.InfinityCategories.F2
