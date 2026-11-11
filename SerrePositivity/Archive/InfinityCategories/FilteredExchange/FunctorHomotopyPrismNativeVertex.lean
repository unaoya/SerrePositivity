module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyPrismVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorPostLaws

/-!
概要：元の全 prism の始点に選択済み作用を施す頂点を、同じ元の普遍証拠の終点へ戻す。
方針：元の始点評価の頂点式と相対後合成の厳密な頂点式を合成する。
規約：元の作用・実始域射を保持。使われ方：指定比較の全自然性の四頂点の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
  (H : SSet.Homotopy F G) (p : C ⟶ B) (s : C ⟶ leftUnstraightening F)
  (hi : s ≫ leftUnstraighteningProjection F = p)
  (w : RelativeExtensionEndpointWitness pointedSpaceProjection
    ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)) (prismEndpoint 0 C)
    (s ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p)

/-- 元の全 prism の始点に施した native 作用の頂点は、同じ普遍証拠の実終点。 -/
lemma functorHomotopyPrismNativeSource_vertex :
    (functorHomotopyPrismSourceEvaluation H p ≫ HomotopyLimits.relativeFunctorPost
      (leftUnstraighteningProjection F) (leftUnstraighteningProjection G)
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).property p).app _
      (relativeFunctorVertex pointedSpaceProjection
        ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)) w.extension w.over) =
      relativeFunctorVertex (leftUnstraighteningProjection G) p
        (functorHomotopySourceCanonicalWitness H p s hi).endpoint
        (functorHomotopySourceCanonicalWitness H p s hi).endpoint_over := by
  change (HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection G)
    (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val
    (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).property p).app _
    ((functorHomotopyPrismSourceEvaluation H p).app _ _) = _
  rw [functorHomotopyPrismSourceEvaluation_vertex H p s hi w]
  exact relativeFunctorPost_vertex _ _ _
    (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).property p s hi

end SerrePositivity.InfinityCategories.F2
