module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IntervalPathHomotopy

/-! 指定ホモトピーを全区間写像ごと curry し、二つの実端点を厳密に回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
variable {K X : SSet.{u}} {f g : K ⟶ X} (H : SSet.Homotopy f g)

def dgGluingHomotopyIntervalPath : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h)

lemma dgGluingHomotopyIntervalPath_start :
    dgGluingHomotopyIntervalPath H ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app X = f := by
  change curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = f
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h) 0]
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ (β_ (Δ[1] : SSet.{u}) K).hom = SSet.ι₀ := rfl
  rw [← Category.assoc, hi, H.h₀]

lemma dgGluingHomotopyIntervalPath_end :
    dgGluingHomotopyIntervalPath H ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 1).app X = g := by
  change curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h) 1]
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ (β_ (Δ[1] : SSet.{u}) K).hom = SSet.ι₁ := rfl
  rw [← Category.assoc, hi, H.h₁]

lemma dgGluingHomotopyIntervalPath_uncurry :
    uncurry (dgGluingHomotopyIntervalPath H) =
      (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h :=
  uncurry_curry _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
