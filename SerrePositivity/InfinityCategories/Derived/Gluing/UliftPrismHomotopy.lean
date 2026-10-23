module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseSimplexFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyRetargetValue
public import SerrePositivity.InfinityCategories.F1.Universe.Homotopy
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-! 全 prism 間の同じ実ホモトピーを、標準区間の同型を保って共通宇宙へ移す。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory HomotopyLimits SSet
open scoped Simplicial
variable {K X : SSet.{u}} {F G : (Δ[1] : SSet.{u}) ⊗ K ⟶ X}

def dgGluingUliftPrismHomotopy (H : SSet.Homotopy F G) :
    SSet.Homotopy (dgGluingUliftSimplexFamily.{u, v} 1 F)
      (dgGluingUliftSimplexFamily.{u, v} 1 G) :=
  stableHomotopyRetarget
    (functorHomotopyPrecomp (uliftSimplicialHomotopy.{u, v} H)
      (((uliftStdSimplexIso.{u, v} 1).inv ▷ (SSet.uliftFunctor.{v, u}).obj K) ≫
        (uliftTensorIso (Δ[1] : SSet.{u}) K).inv))
    (Category.assoc _ _ _) (Category.assoc _ _ _)

end SerrePositivity.InfinityCategories
