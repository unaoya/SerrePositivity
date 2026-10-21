module

public import SerrePositivity.InfinityCategories.F2.FunctorTriangleRightComparison
public import SerrePositivity.InfinityCategories.F2.FunctorTriangleComparisonValues

/-!
概要：元の全三角形の右辺の指定比較の終点像は、同じ全三角形の指定終点比較そのもの。
方針：端点表示変更の指定値を保持し、同じ全族の辺制限と終点評価の因子分解を使う。
規約：元の指定比較を保持。使われ方：右辺の自然性を三角形の native 合成比較へ繋ぐ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle a b c} {p : C ⟶ B} {s : C ⟶ leftUnstraightening F}
  (w : FunctorTrianglePointedWitness T p s) (hi : s ≫ leftUnstraighteningProjection F = p)
local notation "z" => functorTrianglePointedCanonicalWitness T p s hi

/-- 元の右辺の指定比較の終点像は、元の同じ全三角形比較の終点像と厳密に一致。 -/
lemma FunctorTrianglePointedWitness.rightActualComparison_eq_endpoint :
    w.rightActualComparison hi = w.endpointComparison hi := by
  let φ := w.rightPrismComparison hi
  let ν := w.comparison hi
  let E := w.edgeMap b 0 T.face_zero
  let R := functorHomotopyPrismTargetEvaluation b p
  have hx := w.edgeMap_vertex b 0 T.face_zero w
  have hy := w.edgeMap_vertex b 0 T.face_zero z
  have hm := vertexIso_map_heq_of_heq φ (VertexIso.map ν E) hx.symm hy.symm
    (w.prismComparison_heq_edge hi b 0 T.face_zero) R
  have hEnd : prismEndpoint 1 C ≫ (stdSimplex.δ (0 : Fin 3) ▷ C) =
      simplexPrismVertex 2 2 C := by
    apply SSet.hom_ext
    intro n
    rfl
  have hf := vertexIso_map_heq ν (w.edgeEndpoint_factor b 0 T.face_zero hEnd)
  have ha : HEq (w.rightActualComparison hi) (VertexIso.map φ R) :=
    vertexIsoOfEq_heq _ (functorHomotopyPrismTargetEvaluation_vertex b p w.middle w.secondWitness)
      (functorHomotopyPrismTargetEvaluation_vertex b p (z).middle (z).secondWitness)
  have hb : HEq (w.endpointComparison hi) (VertexIso.map ν w.endpointMap) :=
    vertexIsoOfEq_heq _ (w.endpointMap_vertex w) (w.endpointMap_vertex z)
  exact eq_of_heq (ha.trans (hm.trans
    ((heq_of_eq (vertexIso_map_comp ν E R)).trans (hf.trans hb.symm))))

end SerrePositivity.InfinityCategories.F2
