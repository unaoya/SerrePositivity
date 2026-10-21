module

public import SerrePositivity.InfinityCategories.F2.FunctorTriangleRightEndpointComparison

/-!
概要：元の右辺の指定自然性から、全終点比較を元の第二始域比較と始点像の native 作用へ表す。
方針：元の指定右辺での比較の恒等性を、明示した元の終点等式で簡約する。
規約：元の指定値と全係数を保持。使われ方：三角形の比較を二辺の比較へ分解する。
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
local notation "u" => functorHomotopySourceCanonicalWitness b p
  (FunctorTrianglePointedWitness.middle z) (FunctorTrianglePointedWitness.middle_projection z)

/-- 元の指定三角形の実終点の頂点は、同じ元の右辺の普遍証拠の終点の頂点。 -/
lemma functorTriangleCanonical_endpoint_second_vertex :
    relativeFunctorVertex (leftUnstraighteningProjection J) p (z).endpoint (z).endpoint_projection =
      relativeFunctorVertex (leftUnstraighteningProjection J) p (u).endpoint (u).endpoint_over := by
  apply Subtype.ext
  exact congrArg functorVertex (congrArg RelativeExtensionEndpointWitness.endpoint
    (functorTriangleCanonical_secondWitness T p s hi))

/-- 元の全終点比較を、元の指定右辺の同じ普遍終点の表示に揃えた値。 -/
def FunctorTrianglePointedWitness.rightEndpointComparison :=
  vertexIsoOfEq (w.endpointComparison hi) rfl
    (functorTriangleCanonical_endpoint_second_vertex (T := T) (p := p) (s := s) hi)

/-- 右辺の元の指定比較の恒等性から、同じ元の第二始域比較との整合を得る。 -/
lemma FunctorTrianglePointedWitness.rightNativeComparison_eq :
    w.rightNativeComparison hi =
      functorHomotopySourceEndpointIso b p w.middle w.middle_projection w.secondWitness ≪≫
        w.rightEndpointComparison hi := by
  have hs := w.right_specified_naturality hi
  rw [w.rightActualComparison_eq_endpoint hi] at hs
  have hv := functorTriangleCanonical_endpoint_second_vertex (T := T) (p := p) (s := s) hi
  have he := vertexIso_square_of_heq (w.rightNativeComparison hi)
    (functorHomotopySourceEndpointIso b p (z).middle (z).middle_projection (z).secondWitness)
    (functorHomotopySourceEndpointIso b p w.middle w.middle_projection w.secondWitness)
    (w.endpointComparison hi) (w.rightNativeComparison hi) (Iso.refl _)
    (functorHomotopySourceEndpointIso b p w.middle w.middle_projection w.secondWitness)
    (w.rightEndpointComparison hi) rfl rfl rfl hv (HEq.rfl)
    (functorTriangleCanonical_second_sourceIso_heq_refl T p s hi) (HEq.rfl)
    (vertexIsoOfEq_heq _ rfl hv).symm hs
  exact (by simpa only [Iso.trans_refl] using he)

end SerrePositivity.InfinityCategories.F2
