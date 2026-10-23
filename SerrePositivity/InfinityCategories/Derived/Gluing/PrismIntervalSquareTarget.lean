module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PrismIntervalSquare

/-! 同じ四角形の標的側で、全 prism の後合成と区間評価の前合成を移し替える。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

lemma dgGluingPrismIntervalSquare_target {K L N X : SSet.{u}}
    (h : (Δ[1] : SSet.{u}) ⊗ K ⟶ L) (q : L ⟶ N) (e : (Δ[1] : SSet.{u}) ⊗ N ⟶ X) :
    dgGluingPrismIntervalSquare (h ≫ q) e =
      dgGluingPrismIntervalSquare h ((Δ[1] ◁ q) ≫ e) := by
  simp only [dgGluingPrismIntervalSquare, whiskerLeft_comp, Category.assoc]

end SerrePositivity.InfinityCategories
