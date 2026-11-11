module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleInitialNativeEvaluation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoConstantValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation

/-!
概要：元の全三角形比較の固定始点の辺像は、native 始点で同じ恒等同型となる。
方針：同じ全族の辺像を元の定値写像へ戻し、定値族の指定値を計算する。
規約：全係数・元の指定比較を保持。使われ方：第一辺・長辺の指定自然性の簡約。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J Q : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle a b c} {p : C ⟶ B} {s : C ⟶ leftUnstraightening F}
  (w : FunctorTrianglePointedWitness T p s) (hi : s ≫ leftUnstraighteningProjection F = p)
  (H : SSet.Homotopy F Q) (i : Fin 3) (hFace : stdSimplex.δ i ≫ T.diagram = curry H.h)
local notation "P" => HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection F)
  (leftUnstraighteningProjection Q)
  (Subtype.val (leftUnstraighteningMappingVertexMap F Q (coherentVertexOfHomotopy H)))
  (Subtype.property (leftUnstraighteningMappingVertexMap F Q (coherentVertexOfHomotopy H))) p
local notation "z" => functorHomotopySourceCanonicalWitness H p s hi

/-- 元の同じ指定辺比較の native 始点像は、元の普遍終点の恒等同型そのもの。 -/
lemma FunctorTrianglePointedWitness.prismComparison_native_heq_refl
    (hStart : prismEndpoint 0 C ≫ (stdSimplex.δ i ▷ C) = simplexPrismVertex 2 0 C) :
    HEq (VertexIso.map (w.prismComparison H i hFace hi)
      (functorHomotopyPrismSourceEvaluation H p ≫ P))
      (Iso.refl (SSet.HomotopyCategory.mk (relativeFunctorVertex
        (leftUnstraighteningProjection Q) p (z).endpoint (z).endpoint_over))) := by
  have := w.choice_contractible.kanComplex
  let ν := w.comparison hi
  let E := w.edgeMap H i hFace
  let f := functorHomotopyPrismSourceEvaluation H p ≫ P
  have hm := vertexIso_map_heq_of_heq (w.prismComparison H i hFace hi) (VertexIso.map ν E)
    (w.edgeMap_vertex H i hFace w).symm
    (w.edgeMap_vertex H i hFace (functorTrianglePointedCanonicalWitness T p s hi)).symm
    (w.prismComparison_heq_edge hi H i hFace) f
  have hc := vertexIso_map_heq_refl_of_eq_const ν _ (w.edgeNative_constant hi H i hFace hStart)
  exact hm.trans ((heq_of_eq (vertexIso_map_comp ν E f)).trans hc)

end SerrePositivity.InfinityCategories.F2
