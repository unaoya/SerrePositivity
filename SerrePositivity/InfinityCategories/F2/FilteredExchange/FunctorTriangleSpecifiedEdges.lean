module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleEndpointEdges
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleCanonicalLongSpecified

/-!
概要：元の指定三角形比較を、同じ全実三角形の辺比較と中間比較の native 像で表す。
方針：長辺の元の指定値と右辺の指定自然性を、明示した同じ終点表示で合成する。
規約：元の指定同型を保持。使われ方：全終点比較を元の二辺の比較へ表す。
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
local notation "α" => functorHomotopySourceEndpointIso c p s hi
  (FunctorTrianglePointedWitness.longWitness z)
local notation "V" => coherentTriangleOfFunctorTriangle T

/-- 元の指定長辺比較の終点だけを、同じ元の二作用の合成の頂点表示へ揃える。 -/
def functorTriangleCanonicalLongEndpointComparison :=
  vertexIsoOfEq α rfl
    (functorTriangleCanonical_endpoint_second_vertex (T := T) (p := p) (s := s) hi)

/-- 元の長辺の自然性は、終点の表示を揃えても同じ元の全終点比較との合成を保つ。 -/
lemma FunctorTrianglePointedWitness.canonicalLongEndpointComparison_eq :
    functorTriangleCanonicalLongEndpointComparison (T := T) (p := p) (s := s) hi =
      functorHomotopySourceEndpointIso c p s hi w.longWitness ≪≫
        w.rightEndpointComparison hi := by
  have hv := functorTriangleCanonical_endpoint_second_vertex (T := T) (p := p) (s := s) hi
  have hr {x y : (relativeFunctorSpace (leftUnstraighteningProjection J) p) _⦋0⦌}
      (h : x = y) : HEq (Iso.refl (SSet.HomotopyCategory.mk x))
        (Iso.refl (SSet.HomotopyCategory.mk y)) := by
    cases h
    rfl
  have h := vertexIso_square_of_heq
    (functorHomotopySourceEndpointIso c p s hi w.longWitness) (w.endpointComparison hi)
    α (Iso.refl _) (functorHomotopySourceEndpointIso c p s hi w.longWitness)
    (w.rightEndpointComparison hi) (functorTriangleCanonicalLongEndpointComparison (T := T) (p
      := p) (s := s) hi) (Iso.refl _)
    rfl rfl hv hv (HEq.rfl) (vertexIsoOfEq_heq _ rfl hv).symm
    (vertexIsoOfEq_heq _ rfl hv).symm (hr hv) (by
      simpa only [Iso.trans_refl] using (w.long_specified_naturality hi).symm)
  simpa only [Iso.trans_refl] using h.symm

/-- 元の指定三角形比較は、同じ全実三角形の三辺の指定比較で表せる。 -/
lemma FunctorTrianglePointedWitness.specifiedTriangle_heq_edges :
    HEq (VertexIso.map (unstraighteningTriangleRelativeVertexIso F G J
      (coherentVertexOfHomotopy a) (coherentVertexOfHomotopy b) (coherentVertexOfHomotopy c)
      (V).diagram (V).first (V).second (V).long)
      (relativeFunctorPre (leftUnstraighteningProjection J) (leftUnstraighteningProjection F) s))
      (functorHomotopySourceEndpointIso c p s hi w.longWitness ≪≫
        ((functorHomotopySourceEndpointIso b p w.middle w.middle_projection w.secondWitness).symm ≪≫
          w.middleNativeComparison hi)) := by
  have h := (functorTriangleCanonicalLongSourceIso_heq_triangle T p s hi).symm
  have hv := functorTriangleCanonical_endpoint_second_vertex (T := T) (p := p) (s := s) hi
  have hn : HEq (functorTriangleCanonicalLongEndpointComparison (T := T) (p := p) (s := s) hi)
    α := vertexIsoOfEq_heq _ rfl hv
  have he := w.canonicalLongEndpointComparison_eq hi
  rw [w.rightEndpointComparison_eq_edges hi] at he
  exact h.trans (hn.symm.trans (heq_of_eq he))

end SerrePositivity.InfinityCategories.F2
