module

public import SerrePositivity.InfinityCategories.F2.FunctorTriangleSpecifiedEdges
public import SerrePositivity.InfinityCategories.F2.FunctorTriangleFirstInverseNative
public import SerrePositivity.InfinityCategories.F2.VertexIsoCompositionTransport

/-!
概要：元の指定三角形比較を、同じ全実持ち上げの三辺の元の指定比較で表す。
方針：中間像を第一比較の逆の native 後合成へ同定し、指定値を保って合成する。
規約：元の指定同型と全係数を保持。使われ方：全三単体の四面の比較と三関係。
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
local notation "V" => coherentTriangleOfFunctorTriangle T

/-- 元の指定三角形比較は、同じ全実持ち上げの長辺・第二辺・第一辺の指定比較の合成。 -/
lemma FunctorTrianglePointedWitness.specifiedTriangle_heq_threeEdges :
    HEq (VertexIso.map (unstraighteningTriangleRelativeVertexIso F G J
      (coherentVertexOfHomotopy a) (coherentVertexOfHomotopy b) (coherentVertexOfHomotopy c)
      (V).diagram (V).first (V).second (V).long)
      (relativeFunctorPre (leftUnstraighteningProjection J) (leftUnstraighteningProjection F) s))
      (functorHomotopySourceEndpointIso c p s hi w.longWitness ≪≫
        ((functorHomotopySourceEndpointIso b p w.middle w.middle_projection w.secondWitness).symm ≪≫
          w.firstInverseNativeComparison hi)) := by
  let β := functorHomotopySourceEndpointIso b p w.middle w.middle_projection w.secondWitness
  have hv := functorTriangleCanonical_middle_native_vertex (T := T) (p := p) (s := s) hi
  have hm := vertexIso_trans_heq_of_heq β.symm (w.middleNativeComparison hi)
    β.symm (w.firstInverseNativeComparison hi) rfl rfl hv (HEq.rfl)
    (w.middleNativeComparison_heq_firstInverseNative hi)
  have ht := vertexIso_trans_heq_of_heq
    (functorHomotopySourceEndpointIso c p s hi w.longWitness)
    (β.symm ≪≫ w.middleNativeComparison hi)
    (functorHomotopySourceEndpointIso c p s hi w.longWitness)
    (β.symm ≪≫ w.firstInverseNativeComparison hi) rfl rfl hv (HEq.rfl) hm
  exact (w.specifiedTriangle_heq_edges hi).trans ht

end SerrePositivity.InfinityCategories.F2
