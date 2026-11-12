module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.NativePointedTriangleFaceSections
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallFiberTriangleMiddle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-!
概要：図式側の辺の切断族の始点評価を、元の小さい fiber の第一作用へ同定する。
方針：相対 curry の評価を展開し、三角形の二面が共有する中間頂点を照合する。
規約：全族の包含後の厳密な式。使われ方：実際の fiber 射への端点表示の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 底上の族の相対 curry を指定点で評価し含めると、元の族の同じ点への制限になる。 -/
lemma relativeCurry_evaluate_ι {K A E B : SSet.{u}} (p : E ⟶ B) (d : K ⟶ B)
    (W : K ⊗ A ⟶ E) (hW : W ≫ p = fst K A ≫ d) (k : K _⦋0⦌) :
    relativeFunctorCurry W hW ≫ relativeFunctorEvaluate p d k ≫
      vertexFiberι p (d.app (Opposite.op ⦋0⦌) k) = lift (SSet.const k) (𝟙 A) ≫ W := by
  rw [relativeFunctorEvaluate_ι]
  change curry W ≫ evaluateFunctorAt k = _
  exact curry_evaluateFunctorAt_vertex W k

/-- 図式側の辺の始点と第一辺の終点は、同じ全三角形の中間頂点である。 -/
lemma pointedTriangleDiagramSource_evaluate_ι {A : SSet.{u + 1}}
    (D : (Δ[2] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
    (W : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hW : W ≫ pointedSpaceProjection = fst Δ[2] A ≫ D) :
    pointedTriangleFaceSections D W hW 0 ≫
      relativeFunctorEvaluate pointedSpaceProjection (stdSimplex.δ (0 : Fin 3) ≫ D)
        (stdSimplex.obj₀Equiv.symm 0) ≫
      vertexFiberι pointedSpaceProjection
        ((stdSimplex.δ (0 : Fin 3) ≫ D).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm 0)) =
        prismEndpoint 1 A ≫ (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ W := by
  rw [pointedTriangleFaceSections, relativeCurry_evaluate_ι]
  have h : lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 A) ≫
      (stdSimplex.δ (0 : Fin 3) ▷ A) =
        prismEndpoint 1 A ≫ (stdSimplex.δ (2 : Fin 3) ▷ A) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    apply Prod.ext
    · apply stdSimplex.ext
      intro i
      rfl
    · rfl
  rw [← Category.assoc, h, Category.assoc]

variable {B : SSet.{u}}
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)
local notation "D" => coherentTransformationPointDiagram T.diagram (ULift.up b)
local notation "H" => coherentSmallFiberPointedTriangle F G J x y T b
local notation "hH" => coherentSmallFiberPointedTriangle_projection F G J x y T b

/-- 元の図式側の切断族の始点評価は、実際の小さい第一 fiber 射の pointed 表示。 -/
lemma coherentSmallFiberTriangleDiagramSource_evaluate_ι :
    pointedTriangleFaceSections D H hH 0 ≫
      relativeFunctorEvaluate pointedSpaceProjection (stdSimplex.δ (0 : Fin 3) ≫ D)
        (stdSimplex.obj₀Equiv.symm 0) ≫
      vertexFiberι pointedSpaceProjection
        ((stdSimplex.δ (0 : Fin 3) ≫ D).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm 0)) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberMap (smallLeftUnstraighteningProjection F)
          (smallLeftUnstraighteningProjection G) (coherentTransformationTotalMap F G x)
          (coherentTransformationTotalMap_projection F G x) b) ≫
        coherentCospanFiberPointedSource G b :=
  (pointedTriangleDiagramSource_evaluate_ι D H hH).trans
    (coherentSmallFiberPointedTriangle_middle_fiber F G J x y T b)

end SerrePositivity.InfinityCategories.F2
