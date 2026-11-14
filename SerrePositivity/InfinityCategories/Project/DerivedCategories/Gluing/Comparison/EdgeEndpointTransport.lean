module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ArrowCalculus.EdgeRepresentation

/-! 同じ実一単体を、指定された端点等式だけで輸送して表現する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet
open scoped _root_.Simplicial

def dgGluingEdgeEndpointTransport {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') (e : X.Edge x y) : X.Edge x' y' :=
  ⟨e.edge, e.src_eq.trans hx, e.tgt_eq.trans hy⟩

lemma dgGluingEdgeRepresentation_of_hom_equivalence_of_eq {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (x y : X _⦋0⦌)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap f x y))
    {x' y' : Y _⦋0⦌} (hx : f.app _ x = x') (hy : f.app _ y = y') (α : Y.Edge x' y') :
    ∃ b : X.Edge x y, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (dgGluingEdgeEndpointTransport hx hy (b.map f)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge α)) := by
  subst x'
  subst y'
  obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingEdgeRepresentation_of_hom_equivalence f x y hf α
  exact ⟨b, hb⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
