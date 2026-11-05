module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalHomMapCriterion
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertexEquivalence

/-! 一端点対の写像空間同値から、実辺の端点固定の表現を取り出す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

lemma dgGluingEdgeRepresentation_of_hom_equivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (x y : X _⦋0⦌)
    (hf : IsSimplicialHomotopyEquivalence (pinchedHomMap f x y))
    (α : Y.Edge (f.app _ x) (f.app _ y)) :
    ∃ b : X.Edge x y, Nonempty (VertexIso
      (intervalMappingVertexOfEdge (b.map f)) (intervalMappingVertexOfEdge α)) := by
  have he := dgGluingIntervalPost_equivalence_of_pinched f x y hf
  obtain ⟨z, ⟨e⟩⟩ := he.choose.isEssentiallySurjective (intervalMappingVertexOfEdge α)
  change VertexIso ((intervalMappingPost f x y).app (Opposite.op ⦋0⦌) z)
    (intervalMappingVertexOfEdge α) at e
  let b := intervalMappingEdgeOfVertex z
  have hb : intervalMappingVertexOfEdge b = z :=
    (intervalMappingEdgeVertexEquiv x y).apply_symm_apply z
  rw [← hb, intervalMappingPost_vertex] at e
  exact ⟨b, ⟨e⟩⟩

end SerrePositivity.InfinityCategories
