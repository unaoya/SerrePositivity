module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionArrowRetracts
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.FunctorComplete

/-!
概要：元の任意の冪等完備化は、辺の全関手 ∞ 圏上でも冪等完備化。
方針：元の後合成の充満忠実性、辺全体の retract と関手圏の coherent 完備性を合わせる。
規約：元の後合成写像そのものを使用し、辺の類だけの圏で代用しない。
使われ方：HA 1.1.3.7 の fiber/cofiber の関手的な延長。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の全辺への後合成そのものは、辺の関手 ∞ 圏の冪等完備化を与える。 -/
lemma IsIdempotentCompletion.arrow {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (f : C ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion ((ihom (Δ[1] : SSet.{u})).map f) := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.functor_isIdempotentComplete Δ[1] hf.1,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful.postcompose hf.2.1 Δ[1], ?_⟩
  intro v
  obtain ⟨a, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) D).surjective v
  obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.arrow_retract f hf a
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b, hb⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
