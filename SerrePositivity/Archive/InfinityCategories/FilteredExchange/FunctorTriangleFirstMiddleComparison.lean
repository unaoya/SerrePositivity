module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleInitialComparisons
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleMiddleComparison

/-!
概要：元の第一辺の指定比較の終点像を、元の同じ全三角形の中間比較へ厳密に同定する。
方針：同じ辺像の値と第一辺の終点評価の中間評価への因子分解を使う。
規約：全係数と指定比較を保持。使われ方：中間比較を元の第一始域比較へ戻す。
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

/-- 元の第一辺の指定比較の終点像は、元の同じ全三角形比較の中間像そのもの。 -/
lemma FunctorTrianglePointedWitness.firstActualComparison_eq_middle :
    w.firstActualComparison hi = w.middleComparison hi := by
  let φ := w.firstPrismComparison hi
  let ν := w.comparison hi
  let E := w.edgeMap a 2 T.face_two
  let R := functorHomotopyPrismTargetEvaluation a p
  have hm := vertexIso_map_heq_of_heq φ (VertexIso.map ν E)
    (w.edgeMap_vertex a 2 T.face_two w).symm (w.edgeMap_vertex a 2 T.face_two z).symm
    (w.prismComparison_heq_edge hi a 2 T.face_two) R
  have hf := vertexIso_map_heq ν w.firstTarget_factor
  have ha : HEq (w.firstActualComparison hi) (VertexIso.map φ R) :=
    vertexIsoOfEq_heq _ (functorHomotopyPrismTargetEvaluation_vertex a p s w.firstWitness)
      (functorHomotopyPrismTargetEvaluation_vertex a p s (z).firstWitness)
  have hb : HEq (w.middleComparison hi) (VertexIso.map ν w.middleMap) :=
    vertexIsoOfEq_heq _ (w.middleMap_vertex w) (w.middleMap_vertex z)
  exact eq_of_heq (ha.trans (hm.trans
    ((heq_of_eq (vertexIso_map_comp ν E R)).trans (hf.trans hb.symm))))

end SerrePositivity.InfinityCategories.F2
