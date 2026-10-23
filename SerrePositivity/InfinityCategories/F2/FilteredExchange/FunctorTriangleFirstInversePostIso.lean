module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorHomotopySourcePostIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleFirstInverseNative
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.VertexIsoCompositionTransport

/-!
概要：第一辺の比較の逆の後合成を、元の後合成の頂点で正規化した始域比較へ戻す。
方針：同じ実辺の頂点等式・逆・後合成を元の指定値を保って順に輸送する。
規約：端点等式を明示。使われ方：四面の比較を同じ六辺の後合成の比較で厳密に表す。
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
local notation "va" => leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)
local notation "vb" => leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)
local notation "P" => HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection G)
  (leftUnstraighteningProjection J) (Subtype.val vb) (Subtype.property vb) p
local notation "A" => functorHomotopySourceCanonicalWitness a p s hi

/-- 元の第一比較の逆の native 像は、元の後合成の始点へ表示した同じ第一比較の逆の像。 -/
lemma FunctorTrianglePointedWitness.firstInverseNativeComparison_heq_sourcePost :
    HEq (w.firstInverseNativeComparison hi)
      (VertexIso.map (functorHomotopySourcePostIso a p s hi w.firstWitness).symm P) := by
  have hx := relativeFunctorPost_vertex _ _ _ (va).property p s hi
  have hi' := vertexIso_symm_heq_of_heq
    (functorHomotopySourceEndpointIso a p s hi w.firstWitness)
    (functorHomotopySourcePostIso a p s hi w.firstWitness) hx.symm rfl
    (functorHomotopySourcePostIso_heq_source a p s hi w.firstWitness).symm
  have hm := vertexIso_map_heq_of_heq
    (functorHomotopySourceEndpointIso a p s hi w.firstWitness).symm
    (functorHomotopySourcePostIso a p s hi w.firstWitness).symm rfl hx.symm hi' P
  exact (vertexIsoOfEq_heq _
    (relativeFunctorPost_vertex _ _ _ (vb).property p w.middle w.middle_projection)
    (relativeFunctorPost_vertex _ _ _ (vb).property p (A).endpoint (A).endpoint_over)).trans hm

end SerrePositivity.InfinityCategories.F2
