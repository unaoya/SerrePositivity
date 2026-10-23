module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTriangleTargetFiberEvaluation

/-!
概要：明示した最後の fiber での評価を、同じ全 pointed 三角形の最終頂点へ戻す。
方針：縮小の同型の往復と頂点の輸送を消し、元の相対 curry の評価式を適用する。
規約：全族の厳密な等式。使われ方：左右の native 最終頂点の fiber 内での一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の小さい最後の fiber の表示を含めると、同じ終点評価そのものになる。 -/
lemma pointedSectionTargetFiber_pointed {B : SSet.{u}}
    (G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
    (e : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
    (hv : e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1) = G.app _ (ULift.up b)) :
    pointedSectionTargetFiber G b e hv ≫ (coherentFiberPointedSourceIso G b).hom ≫
      vertexFiberι pointedSpaceProjection (G.app (Opposite.op ⦋0⦌) (ULift.up b)) =
      relativeFunctorEvaluate pointedSpaceProjection e (stdSimplex.obj₀Equiv.symm 1) ≫
        vertexFiberι pointedSpaceProjection (e.app _ (stdSimplex.obj₀Equiv.symm 1)) := by
  simp only [pointedSectionTargetFiber, Category.assoc, Iso.inv_hom_id_assoc,
    vertexFiberTransport_ι pointedSpaceProjection hv]

/-- 任意の全 pointed 三角形の切断族の最後の fiber 評価は、その同じ最終頂点を保持する。 -/
lemma pointedTriangleTargetFiberEvaluation_pointed {B : SSet.{u}} {A : SSet.{u + 1}}
    (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
    (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)
    (D : (Δ[2] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
    (hD : D = coherentTransformationPointDiagram T.diagram (ULift.up b))
    (W : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hW : W ≫ pointedSpaceProjection = fst Δ[2] A ≫ D) :
    (pointedTriangleFaceSections D W hW 0 ≫
      coherentTriangleTargetFiberEvaluation F G J x y T b D hD) ≫
      (coherentFiberPointedSourceIso J b).hom ≫
        vertexFiberι pointedSpaceProjection (J.app _ (ULift.up b)) =
      prismEndpoint 1 A ≫ (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ W := by
  rw [Category.assoc, coherentTriangleTargetFiberEvaluation, pointedSectionTargetFiber_pointed]
  exact pointedTriangleDiagramTarget_evaluate_ι D W hW

end SerrePositivity.InfinityCategories.F2
