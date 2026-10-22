module
public import SerrePositivity.InfinityCategories.F1.SmallSimplicialSet
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentFullSubcategoryRestriction

/-! # 小さい対象集合を持つ、元の豊穣圏の coherent nerve の小ささ -/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 小さい対象間の豊穣関手は、対象作用とそれを固定した Hom 作用の組へ単射で入る。 -/
theorem small_enrichedFunctor {D : Type v} {E : Type w}
    [Small.{u} D] [Small.{u} E]
    [EnrichedCategory SSet.{u} D] [EnrichedCategory SSet.{u} E] :
    Small.{u} (EnrichedFunctor SSet.{u} D E) := by
  let code (F : EnrichedFunctor SSet.{u} D E) :
      Σ obj : D → E, {G : EnrichedFunctor SSet.{u} D E // G.obj = obj} :=
    ⟨F.obj, F, rfl⟩
  apply small_of_injective (f := code)
  intro F G h
  exact congrArg (fun a => a.2.val) h

/-- Hom の宇宙と対象の小ささが揃えば、coherent nerve の全次数も同じ宇宙で小さい。 -/
theorem small_simplicialNerve_obj {D : Type v} [Category.{u} D] [SimplicialCategory D]
    [Small.{u} D] (n : SimplexCategoryᵒᵖ) : Small.{u} ((SimplicialNerve D).obj n) :=
  small_enrichedFunctor

end SerrePositivity.KST.Fibration
