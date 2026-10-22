module
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPathHomotopy

/-! 指定ホモトピーを全区間写像ごと curry し、二つの実端点を厳密に回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
variable {K X : SSet.{u}} {f g : K ⟶ X} (H : SSet.Homotopy f g)

def dgGluingHomotopyIntervalPath : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h)

lemma dgGluingHomotopyIntervalPath_start :
    dgGluingHomotopyIntervalPath H ≫ (F2.intervalEndpointNatTrans 0).app X = f := by
  change curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h) ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = f
  rw [curry_evaluateFunctorAt_interval ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h) 0]
  have hi : prismEndpoint 0 K ≫ (β_ (Δ[1] : SSet.{u}) K).hom = SSet.ι₀ := rfl
  rw [← Category.assoc, hi, H.h₀]

lemma dgGluingHomotopyIntervalPath_end :
    dgGluingHomotopyIntervalPath H ≫ (F2.intervalEndpointNatTrans 1).app X = g := by
  change curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h) ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g
  rw [curry_evaluateFunctorAt_interval ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h) 1]
  have hi : prismEndpoint 1 K ≫ (β_ (Δ[1] : SSet.{u}) K).hom = SSet.ι₁ := rfl
  rw [← Category.assoc, hi, H.h₁]

lemma dgGluingHomotopyIntervalPath_uncurry :
    uncurry (dgGluingHomotopyIntervalPath H) =
      (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h :=
  uncurry_curry _

end SerrePositivity.InfinityCategories
