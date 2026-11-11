module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopySourceWrapped
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionWitnessDataEquality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UnstraighteningSourceFamilyComparison

/-!
概要：同じ実始域を持つ元の prism 証拠を、F1 の既存の指定始域比較へそのまま渡す。
方針：元の普遍 prism と実 prism の同じ始点・底・終点を一点パラメータで保持する。
規約：既存の指定比較を再利用。使われ方：長辺三証拠の始域比較の成分との同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
  (H : SSet.Homotopy F G) (p : C ⟶ B) (s : C ⟶ leftUnstraightening F)
  (hi : s ≫ leftUnstraighteningProjection F = p)

/-- 元の普遍 prism とその選択済み作用を、同じ全始点・底・実終点の証拠にする。 -/
def functorHomotopySourceCanonicalWitness :
    RelativeExtensionEndpointWitness pointedSpaceProjection
      ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)) (prismEndpoint 0 C)
      (s ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p where
  extension := functorHomotopyPointedPrism H s
  over := by rw [functorHomotopyPointedPrism_projection, hi]
  initial := functorHomotopyPointedPrism_source H s
  endpoint := s ≫ (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val
  endpoint_over := by
    change (s ≫ (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val) ≫
      leftUnstraighteningProjection G = p
    rw [Category.assoc,
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).property, hi]
  evaluate := functorHomotopyPointedPrism_target H s

variable (w : RelativeExtensionEndpointWitness pointedSpaceProjection
  ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)) (prismEndpoint 0 C)
  (s ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p)

/-- 同じ元の普遍 prism と実 prism の指定終点比較。 -/
def functorHomotopySourceEndpointIso :=
  (functorHomotopySourceCanonicalWitness H p s hi).iso w
    (prismEndpoint_zero_leftAnodyne C) w.initial_base w.endpoint_base

/-- 元の実 prism と実終点を、F1 の同じ指定始域比較へそのまま渡す。 -/
def functorHomotopySourceFamilyComparison :=
  unstraighteningSourceFamilyComparisonIso F G p s hi
    (SSet.const (coherentVertexOfHomotopy H) : (Δ[0] : SSet.{u + 1}) ⟶ _)
    (functorHomotopySourceWrappedMap H p s w)
    (functorHomotopySourceWrappedMap_projection H p s w)
    (functorHomotopySourceWrappedPrism H p s w)
    (functorHomotopySourceWrappedPrism_source H p s w)
    (functorHomotopySourceWrappedPrism_target H p s w)
    (functorHomotopySourceWrappedPrism_projection H p s w)

end SerrePositivity.InfinityCategories.F2
