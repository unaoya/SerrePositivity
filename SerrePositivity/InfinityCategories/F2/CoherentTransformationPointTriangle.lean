module

public import SerrePositivity.InfinityCategories.F2.CoherentTransformationPointEdge
public import SerrePositivity.InfinityCategories.F2.SpaceTriangleIso

/-!
概要：元の coherent 合成三角形を各点の実際の二単体と三つの指定辺に戻す。
方針：元の全図式の制限へ Yoneda を適用し、全三辺を元の評価辺と同定する。
規約：二単体も辺も選び直さない。使われ方：各点の元の引き戻し錐の普遍性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌}
  {y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌}
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)

/-- 概要：元の全合成三角形の一点評価の二単体。
方針：元の図式の制限の Yoneda 単体。
規約：元の二単体を保持。使われ方：各点の指定可換同型。 -/
def coherentTransformationPointTriangle : SpaceInfinity.{u} _⦋2⦌ :=
  SSet.yonedaEquiv (coherentTransformationPointDiagram T.diagram b)

/-- 概要：一点評価の第一辺は元の第一変換の指定評価辺そのもの。
方針：全第一面の厳密な制限。規約：一次単体の等式。使われ方：各点の第一脚。 -/
lemma coherentTransformationPointTriangle_first :
    SpaceInfinity.δ 2 (coherentTransformationPointTriangle T b) =
      (functorEdgeAt (intervalMappingEdgeOfVertex x) b).edge := by
  rw [coherentTransformationPointTriangle, ← stdSimplex.yonedaEquiv_δ_comp,
    coherentTransformationPointDiagram_first, coherentTransformationPointDiagram_edge,
    Equiv.apply_symm_apply]

/-- 概要：一点評価の第二辺は元の第二変換の指定評価辺そのもの。
方針：全第二面の厳密な制限。規約：一次単体の等式。使われ方：各点の第二脚。 -/
lemma coherentTransformationPointTriangle_second :
    SpaceInfinity.δ 0 (coherentTransformationPointTriangle T b) =
      (functorEdgeAt (intervalMappingEdgeOfVertex y) b).edge := by
  rw [coherentTransformationPointTriangle, ← stdSimplex.yonedaEquiv_δ_comp,
    coherentTransformationPointDiagram_second, coherentTransformationPointDiagram_edge,
    Equiv.apply_symm_apply]

/-- 概要：一点評価の長辺は元の指定長変換の指定評価辺そのもの。
方針：全長辺の厳密な制限。規約：一次単体の等式。使われ方：共通長辺の照合。 -/
lemma coherentTransformationPointTriangle_long :
    SpaceInfinity.δ 1 (coherentTransformationPointTriangle T b) =
      (functorEdgeAt (intervalMappingEdgeOfVertex T.diagonal) b).edge := by
  rw [coherentTransformationPointTriangle, ← stdSimplex.yonedaEquiv_δ_comp,
    coherentTransformationPointDiagram_long, coherentTransformationPointDiagram_edge,
    Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.F2
