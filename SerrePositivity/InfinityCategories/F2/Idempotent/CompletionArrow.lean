module

public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionArrowRetracts
public import SerrePositivity.InfinityCategories.F2.Idempotent.FunctorComplete

/-!
概要：元の任意の冪等完備化は、辺の全関手 ∞ 圏上でも冪等完備化。
方針：元の後合成の充満忠実性、辺全体の retract と関手圏の coherent 完備性を合わせる。
規約：元の後合成写像そのものを使用し、辺の類だけの圏で代用しない。
使われ方：HA 1.1.3.7 の fiber/cofiber の関手的な延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全辺への後合成そのものは、辺の関手 ∞ 圏の冪等完備化を与える。 -/
lemma IsIdempotentCompletion.arrow {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (f : C ⟶ D) (hf : IsIdempotentCompletion f) :
    IsIdempotentCompletion ((ihom (Δ[1] : SSet.{u})).map f) := by
  refine ⟨functor_isIdempotentComplete Δ[1] hf.1,
    IsFullyFaithful.postcompose hf.2.1 Δ[1], ?_⟩
  intro v
  obtain ⟨a, rfl⟩ := (functorVertexEquiv (Δ[1] : SSet.{u}) D).surjective v
  obtain ⟨b, hb⟩ := IsIdempotentCompletion.arrow_retract f hf a
  exact ⟨functorVertex b, hb⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
