module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseSimplexFamilies
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseIntervalHom

/-! 全 prism の宇宙移送は、区間関手空間の標準同型による curry の移送と厳密に一致。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed
open scoped _root_.Simplicial

lemma dgGluingUliftPrism_uncurry {K X : SSet.{u}}
    (p : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{u, v} 1 (uncurry p) =
      uncurry ((SSet.uliftFunctor.{v, u}).map p ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftIntervalHomIso.{u, v} X).hom) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨t, ⟨k⟩⟩
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
