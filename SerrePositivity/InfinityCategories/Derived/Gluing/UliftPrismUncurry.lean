module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseSimplexFamilies
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseIntervalHom

/-! 全 prism の宇宙移送は、区間関手空間の標準同型による curry の移送と厳密に一致。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed HomotopyLimits
open scoped Simplicial

lemma dgGluingUliftPrism_uncurry {K X : SSet.{u}}
    (p : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    dgGluingUliftSimplexFamily.{u, v} 1 (uncurry p) =
      uncurry ((SSet.uliftFunctor.{v, u}).map p ≫ (uliftIntervalHomIso.{u, v} X).hom) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨t, ⟨k⟩⟩
  rfl

end SerrePositivity.InfinityCategories
