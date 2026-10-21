module

public import SerrePositivity.InfinityCategories.F2.FunctorTriangleInitialComparisons

/-!
概要：元の長辺の指定比較の終点像を、元の同じ全三角形の終点比較へ厳密に同定する。
方針：元の辺像の値と同じ最終頂点への終点評価の因子分解を使う。
規約：全係数と指定比較を保持。使われ方：元の指定三角形比較と長辺の始域比較の接続。
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

/-- 元の長辺の指定比較の終点像は、元の同じ全三角形比較の全終点像そのもの。 -/
lemma FunctorTrianglePointedWitness.longActualComparison_eq_endpoint :
    w.longActualComparison hi = w.endpointComparison hi := by
  let φ := w.longPrismComparison hi
  let ν := w.comparison hi
  let E := w.edgeMap c 1 T.face_one
  let R := functorHomotopyPrismTargetEvaluation c p
  have hm := vertexIso_map_heq_of_heq φ (VertexIso.map ν E)
    (w.edgeMap_vertex c 1 T.face_one w).symm (w.edgeMap_vertex c 1 T.face_one z).symm
    (w.prismComparison_heq_edge hi c 1 T.face_one) R
  have hEnd : prismEndpoint 1 C ≫ (stdSimplex.δ (1 : Fin 3) ▷ C) =
      simplexPrismVertex 2 2 C := by
    apply SSet.hom_ext
    intro n
    rfl
  have hf := vertexIso_map_heq ν (w.edgeEndpoint_factor c 1 T.face_one hEnd)
  have ha : HEq (w.longActualComparison hi) (VertexIso.map φ R) :=
    vertexIsoOfEq_heq _ (functorHomotopyPrismTargetEvaluation_vertex c p s w.longWitness)
      (functorHomotopyPrismTargetEvaluation_vertex c p s (z).longWitness)
  have hb : HEq (w.endpointComparison hi) (VertexIso.map ν w.endpointMap) :=
    vertexIsoOfEq_heq _ (w.endpointMap_vertex w) (w.endpointMap_vertex z)
  exact eq_of_heq (ha.trans (hm.trans
    ((heq_of_eq (vertexIso_map_comp ν E R)).trans (hf.trans hb.symm))))

end SerrePositivity.InfinityCategories.F2
