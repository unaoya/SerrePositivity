module
public import SerrePositivity.InfinityCategories.Core.EquivalencePath

/-! 区間第一因子の全 prism とその二端から、同じ全円柱写像のホモトピーを作る。 -/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

def dgGluingHomotopyOfPrism {K X : SSet.{u}} {f g : K ⟶ X}
    (P : (Δ[1] : SSet.{u}) ⊗ K ⟶ X)
    (h₀ : prismEndpoint 0 K ≫ P = f) (h₁ : prismEndpoint 1 K ≫ P = g) :
    SSet.Homotopy f g where
  h := (β_ K (Δ[1] : SSet.{u})).hom ≫ P
  h₀ := by
    have hi : SSet.ι₀ ≫ (β_ K (Δ[1] : SSet.{u})).hom = prismEndpoint 0 K := rfl
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ P) hi).trans h₀)
  h₁ := by
    have hi : SSet.ι₁ ≫ (β_ K (Δ[1] : SSet.{u})).hom = prismEndpoint 1 K := rfl
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ P) hi).trans h₁)
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories
