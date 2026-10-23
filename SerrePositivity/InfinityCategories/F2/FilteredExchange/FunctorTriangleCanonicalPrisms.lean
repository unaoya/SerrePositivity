module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleCanonicalEndpoints
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorHomotopySourceIdentity

/-!
概要：元の指定三角形の第一辺・右辺の証拠は、元の同じ普遍 prism の証拠そのもの。
方針：実延長と実終点を厳密に同定し、同じ証拠の指定比較の恒等性へ戻す。
規約：元の指定比較を保持。使われ方：全三角形の右辺比較の自然性の簡約。
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
  (T : FunctorCompositionTriangle a b c) (p : C ⟶ B) (s : C ⟶ leftUnstraightening F)
  (hi : s ≫ leftUnstraighteningProjection F = p)
local notation "w" => functorTrianglePointedCanonicalWitness T p s hi

/-- 元の指定三角形の第一辺の全証拠は、同じ元の第一変換の普遍証拠そのもの。 -/
lemma functorTriangleCanonical_firstWitness :
    (w).firstWitness = functorHomotopySourceCanonicalWitness a p s hi :=
  RelativeExtensionEndpointWitness.eq_of_extension_endpoint _ _
    (functorTriangleCanonical_first_extension T p s hi) (functorTriangleCanonical_middle T p s hi)

/-- 元の指定三角形の右辺の実延長は、元の実中間頂点での同じ普遍 prism。 -/
lemma functorTriangleCanonical_second_extension :
    (w).secondWitness.extension = functorHomotopyPointedPrism b (w).middle := by
  calc
    _ = (Δ[1] ◁ s) ≫ (stdSimplex.δ (0 : Fin 3) ▷ leftUnstraightening F) ≫
        functorTrianglePointedLift T := by
      apply SSet.hom_ext
      intro n
      rfl
    _ = _ := (functorTrianglePointedLift_second T s).trans
      (congrArg (fun t => functorHomotopyPointedPrism b t)
        (functorTriangleCanonical_middle T p s hi).symm)

/-- 元の指定三角形の右辺の全証拠は、元の同じ第二変換の普遍証拠そのもの。 -/
lemma functorTriangleCanonical_secondWitness :
    (w).secondWitness = functorHomotopySourceCanonicalWitness b p (w).middle
      (w).middle_projection := by
  apply RelativeExtensionEndpointWitness.eq_of_extension_endpoint
  · exact functorTriangleCanonical_second_extension T p s hi
  · change (w).endpoint = (w).middle ≫
      (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).val
    simp only [functorTriangleCanonical_middle, functorTriangleCanonical_endpoint, Category.assoc]

/-- 元の指定三角形の右辺では、元の指定始域比較は同じ選択済み作用の恒等同型。 -/
lemma functorTriangleCanonical_second_sourceIso_heq_refl :
    HEq (functorHomotopySourceEndpointIso b p (w).middle (w).middle_projection (w).secondWitness)
      (Iso.refl (SSet.HomotopyCategory.mk (relativeFunctorVertex
        (leftUnstraighteningProjection J) p
        (functorHomotopySourceCanonicalWitness b p (w).middle (w).middle_projection).endpoint
        (functorHomotopySourceCanonicalWitness b p (w).middle
          (w).middle_projection).endpoint_over))) := by
  have hw := functorTriangleCanonical_secondWitness T p s hi
  exact functorHomotopySourceEndpointIso_heq_refl b p (w).middle (w).middle_projection
    (w).secondWitness (congrArg RelativeExtensionEndpointWitness.extension hw)
    (congrArg RelativeExtensionEndpointWitness.endpoint hw)

end SerrePositivity.InfinityCategories.F2
