module

public import SerrePositivity.InfinityCategories.F1.SimplexShapeFamilyPushout

/-!
概要：任意の底の pushout を単体圏の nerve の pushout へ写す。
方針：各次数の射列を作用素の列と初単体の依存和に直し、係数の pushout を使う。
規約：境界を貼る射に単射性を仮定しない。
使われ方：一般のセル付加に対する反転関手の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 任意の底の pushout は、実際の単体圏の nerve でも pushout となる。 -/
lemma transportSimplexNerve_isPushout {A B C D : SSet.{u}}
    {i : A ⟶ B} {g : A ⟶ C} {k : B ⟶ D} {j : C ⟶ D} (h : IsPushout i g k j) :
    IsPushout (nerveMap (transportSimplexFunctor i)) (nerveMap (transportSimplexFunctor g))
      (nerveMap (transportSimplexFunctor k)) (nerveMap (transportSimplexFunctor j)) := by
  apply IsPushout.of_forall_isPushout_app
  rintro ⟨⟨n⟩⟩
  have hs := simplexShapeFamily_isPushout
    (fun τ : ComposableArrows SimplexCategoryᵒᵖ n ↦ h.app (τ.obj 0))
  apply hs.of_iso' (transportSimplexChainEquiv A n).toIso (transportSimplexChainEquiv B n).toIso
    (transportSimplexChainEquiv C n).toIso (transportSimplexChainEquiv D n).toIso
  all_goals rfl

/-- 任意の底の pushout では、指定辺を反転する関手の制限が実際の pullback をなす。 -/
lemma transportSimplexInverting_isPullback_of_isPushout {A B C D : SSet.{u}}
    {i : A ⟶ B} {g : A ⟶ C} {k : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout i g k j) (E : SSet.{u}) :
    IsPullback (transportSimplexInvertingRestriction j E)
      (transportSimplexInvertingRestriction k E)
      (transportSimplexInvertingRestriction g E)
      (transportSimplexInvertingRestriction i E) :=
  transportSimplexInverting_isPullback_of_nerve_isPushout (transportSimplexNerve_isPushout h) E

/-- 底の単射は、実際の単体圏の nerve でも単射となる。 -/
instance transportSimplexNerveMap_mono {B D : SSet.{u}} (f : B ⟶ D) [Mono f] :
    Mono (nerveMap (transportSimplexFunctor f)) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro σ τ h
  apply (transportSimplexChainEquiv B n).injective
  have he := congrArg (transportSimplexChainEquiv D n) h
  change (simplexShapeFamilyMap
    (fun s : ComposableArrows SimplexCategoryᵒᵖ n ↦ f.app (s.obj 0)))
      (transportSimplexChainEquiv B n σ) =
    (simplexShapeFamilyMap
      (fun s : ComposableArrows SimplexCategoryᵒᵖ n ↦ f.app (s.obj 0)))
      (transportSimplexChainEquiv B n τ) at he
  exact (mono_iff_injective (simplexShapeFamilyMap
    (fun s : ComposableArrows SimplexCategoryᵒᵖ n ↦ f.app (s.obj 0)))).mp inferInstance he

end SerrePositivity.InfinityCategories
