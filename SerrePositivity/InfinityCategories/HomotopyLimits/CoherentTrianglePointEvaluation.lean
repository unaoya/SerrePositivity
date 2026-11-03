module
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTransformationVertexTriangle

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTransformationPoint
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.SpaceTriangleFaces

/-!
概要：元の coherent 合成三角形を一点で評価し、元の三辺と Kan 合成ホモトピーを回収する。
方針：同じ指定図式を元の底の頂点と一点パラメーターへ制限し、全三面を厳密に計算する。
規約：底の quasicategory 性は不要。元の三角形と全一単体を保持する。
使われ方：有限反復射影の後続脚の合成ホモトピー。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元のパラメーター付き三角形の一点制限は、全ての元の面と厳密に可換。 -/
lemma triangleAtParameter_face {A X : SSet.{u + 1}}
    (H : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ X) (a : A _⦋0⦌) (i : Fin 3) :
    X.δ i (SSet.yonedaEquiv (lift (𝟙 (Δ[2] : SSet.{u + 1})) (SSet.const a) ≫ H)) =
      SSet.yonedaEquiv (lift (𝟙 (Δ[1] : SSet.{u + 1})) (SSet.const a) ≫
        ((stdSimplex.δ i ▷ A) ≫ H)) := by
  rw [← stdSimplex.yonedaEquiv_δ_comp]
  congr 1

variable {B : SSet.{u + 1}} (F G J : B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : F2.CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)

/-- 元の選択済み合成三角形を、元の底の一点で評価した実際の二単体。 -/
def coherentTransformationTriangleAt : SpaceInfinity.{u} _⦋2⦌ :=
  SSet.yonedaEquiv (lift (𝟙 (Δ[2] : SSet.{u + 1}))
    (SSet.const (b, SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1})))) ≫ T.diagram)

/-- 元の第一面は元の第一変換辺の評価そのもの。 -/
lemma coherentTransformationTriangleAt_two :
    SpaceInfinity.δ 2 (coherentTransformationTriangleAt F G J x y T b) =
      (evaluateFunctorAt b).app (Opposite.op ⦋1⦌) (intervalMappingEdgeOfVertex x).edge := by
  rw [coherentTransformationTriangleAt, triangleAtParameter_face, T.first,
    coherentTransformationFamilyDiagram_at, Equiv.apply_symm_apply]
  rfl

/-- 元の第二面は元の第二変換辺の評価そのもの。 -/
lemma coherentTransformationTriangleAt_zero :
    SpaceInfinity.δ 0 (coherentTransformationTriangleAt F G J x y T b) =
      (evaluateFunctorAt b).app (Opposite.op ⦋1⦌) (intervalMappingEdgeOfVertex y).edge := by
  rw [coherentTransformationTriangleAt, triangleAtParameter_face, T.second,
    coherentTransformationFamilyDiagram_at, Equiv.apply_symm_apply]
  rfl

/-- 元の長辺面は元の選択済み長辺の評価そのもの。 -/
lemma coherentTransformationTriangleAt_one :
    SpaceInfinity.δ 1 (coherentTransformationTriangleAt F G J x y T b) =
      (evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
        (intervalMappingEdgeOfVertex T.diagonal).edge := by
  rw [coherentTransformationTriangleAt, triangleAtParameter_face, T.long,
    coherentTransformationFamilyDiagram_at, Equiv.apply_symm_apply]
  rfl

/-- 元の評価三辺を元の Kan 射で表示すると、同じ三角形が元の合成ホモトピーを与える。 -/
def coherentTransformationTriangleAtHomotopy {K L M : KanObject.{u}}
    (f : K ⟶ L) (g : L ⟶ M) (h : K ⟶ M)
    (hf : (evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
      (intervalMappingEdgeOfVertex x).edge = (coherentNerveEdge f).edge)
    (hg : (evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
      (intervalMappingEdgeOfVertex y).edge = (coherentNerveEdge g).edge)
    (hh : (evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
      (intervalMappingEdgeOfVertex T.diagonal).edge = (coherentNerveEdge h).edge) :
    SSet.Homotopy h (f ≫ g) :=
  F2.spaceInfinityTriangleHomotopy_of_faces f g h (coherentTransformationTriangleAt F G J x y T b)
    ((coherentTransformationTriangleAt_two F G J x y T b).trans hf)
    ((coherentTransformationTriangleAt_zero F G J x y T b).trans hg)
    ((coherentTransformationTriangleAt_one F G J x y T b).trans hh)

end SerrePositivity.InfinityCategories.HomotopyLimits
