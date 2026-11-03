module

public import SerrePositivity.InfinityCategories.F2.Idempotent.PresheafCompletionValues
public import SerrePositivity.InfinityCategories.F2.Idempotent.PresheafDiagramRecovery
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.SmallUnstraighteningFunctorIso
public import SerrePositivity.InfinityCategories.Core.FunctorIsoTransport

/-!
概要：元の全部分圏の冪等完備化に沿って、冪等完備な標的への全関手を延長する。
方針：実際の前層値の延長を構成して元の標的へ戻し、元の制限の全自然同型を回収する。
規約：延長の存在・局所余極限・各値の retract 条件を未証明の入力に置かない。
使われ方：HTT 5.1.4.8、全関手 ∞ 圏への制限の本質的全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全部分圏の冪等完備化から、冪等完備な標的へ全関手を全自然同型まで延長する。 -/
lemma exists_extension_to_complete_of_full_inclusion {K C E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory E]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsIdempotentCompletion δ)
    (hE : IsIdempotentComplete E) (F : K ⟶ E) :
    ∃ H : C ⟶ E, Nonempty (FunctorIso (δ ≫ H) F) := by
  obtain ⟨G, hG, hval⟩ := exists_presheafCompletion_extension δ hδ F
  obtain ⟨H, ⟨hH⟩⟩ := exists_diagram_of_retract_presheaves hE G hval
  have hp := hH.precomp ((SSet.uliftFunctor.{u + 1, u}).map δ)
  have h₀ : FunctorIso
      (((SSet.uliftFunctor.{u + 1, u}).map δ ≫
        (SSet.uliftFunctor.{u + 1, u}).map H) ≫ yonedaInfinityMap E)
      ((SSet.uliftFunctor.{u + 1, u}).map F ≫ yonedaInfinityMap E) :=
    functorIsoOfEq hp (Category.assoc _ _ _).symm hG
  have h₁ : FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (δ ≫ H) ≫ yonedaInfinityMap E)
      ((SSet.uliftFunctor.{u + 1, u}).map F ≫ yonedaInfinityMap E) := by
    simpa only [Functor.map_comp] using h₀
  have h₂ := (yonedaInfinityMap_isFullyFaithful E).preimageFunctorIso h₁
  exact ⟨H, ⟨functorIsoDown h₂⟩⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
