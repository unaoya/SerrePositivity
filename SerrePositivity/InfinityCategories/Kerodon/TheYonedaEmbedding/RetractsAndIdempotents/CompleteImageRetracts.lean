module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletenessEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompleteSubcomplexRetracts
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-!
概要：冪等完備な元の ∞ 圏の充満忠実な像は、同型を除いて retract に閉じる。
方針：元の頂点像への同値で coherent 完備性を移し、同じ全部分圏内で分裂を回収する。
規約：元の関手と元の指定 retract の頂点を保持する。
使われ方：HTT 5.1.4.8 の Yoneda 本質像の retract 閉性。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 冪等完備な元の圏の充満忠実な頂点像は、元の全部分圏として冪等完備。 -/
lemma IsIdempotentComplete.fullVertexImage {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C)
    (f : C ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices D
      (fun y ↦ ∃ x, f.app (Opposite.op ⦋0⦌) x = y)) :=
  hC.of_equivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.fullSubcomplexVertexImageLift_isQCatEquivalence f hf).choose

/-- 冪等完備な元の圏の像の指定 retract は、元の別の対象の像と実際に同型。 -/
lemma IsIdempotentComplete.retract_iso_in_image {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C)
    (f : C ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) (c : C _⦋0⦌) (d : D _⦋0⦌)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction d (f.app (Opposite.op ⦋0⦌) c)) :
    ∃ c' : C _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso d (f.app (Opposite.op ⦋0⦌) c')) := by
  let P := fun y ↦ ∃ x, f.app (Opposite.op ⦋0⦌) x = y
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P f (fun x ↦ ⟨x, rfl⟩)
  obtain ⟨z, hz⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retract_iso_in_complete_fullSubcomplex P (hC.fullVertexImage f hf)
    (e.app (Opposite.op ⦋0⦌) c) d r
  obtain ⟨c', hc'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex z
  exact ⟨c', hc'.symm ▸ hz⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
