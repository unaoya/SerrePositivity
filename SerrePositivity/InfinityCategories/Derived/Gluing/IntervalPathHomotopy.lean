module
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

/-! 任意パラメーター上の実区間族を、同じ全区間写像を持つ端点間ホモトピーへ読む。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial

def dgGluingIntervalPathHomotopy {K X : SSet.{u}}
    (p : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    SSet.Homotopy (p ≫ (F2.intervalEndpointNatTrans 0).app X)
      (p ≫ (F2.intervalEndpointNatTrans 1).app X) where
  h := (β_ K (Δ[1] : SSet.{u})).hom ≫ uncurry p
  h₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  h₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories
