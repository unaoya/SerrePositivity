module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopySourceComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoEndpointTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorPostLaws

/-!
概要：元の実 prism の指定始域比較を、元の相対後合成の頂点そのものの始点で保持する。
方針：同じ native 作用の厳密な頂点式で、元の指定同型の始点表示だけを揃える。
規約：元の指定値を保持。使われ方：四面をホモトピー圏上の同じ六比較で表す。
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
local notation "v" => leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)

/-- 同じ元の指定始域比較を、元の native 後合成の頂点を始点として保持する。 -/
def functorHomotopySourcePostIso :=
  vertexIsoOfEq (functorHomotopySourceEndpointIso H p s hi w)
    (relativeFunctorPost_vertex _ _ _ (v).property p s hi).symm rfl

/-- native 後合成の頂点への表示変更は、元の同じ実 prism の指定比較の値を保持する。 -/
lemma functorHomotopySourcePostIso_heq_source :
    HEq (functorHomotopySourcePostIso H p s hi w)
      (functorHomotopySourceEndpointIso H p s hi w) :=
  vertexIsoOfEq_heq _ (relativeFunctorPost_vertex _ _ _ (v).property p s hi).symm rfl

end SerrePositivity.InfinityCategories.F2
