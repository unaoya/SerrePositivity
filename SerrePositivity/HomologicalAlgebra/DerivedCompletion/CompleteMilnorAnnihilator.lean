module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionReconstruction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorAnnihilator

/-! # 完備対象の標準Koszul再構成を通じた一様零化

holim比較を追加の入力にせず、実導来完備性と標準単位から比較同型を供給する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 任意の完備導来対象を、選ばれた代表複体の標準Koszul塔から再構成する。 -/
def completeDerivedKoszulHomotopyLimitIso (a : R) (X : ConcreteDerivedCategory R)
    (hX : IsComplete R a X) :
    X ≅ complexTowerHomotopyLimitObject R
      (complexPowerKoszulStage R a (DerivedCategory.Q.objPreimage X))
      (complexPowerKoszulTransition R a (DerivedCategory.Q.objPreimage X)) := by
  let K := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj K ≅ X := DerivedCategory.Q.objObjPreimageIso X
  exact e.symm ≪≫ complexCompletionUnitIso R a K (isComplete_of_iso R a e.symm hX)

/-- 任意の完備導来対象に対する標準Koszul塔からの一様指数の移送。
指数Nは全段と隣接二次数に共通とし、比較同型は入力として要求しない。 -/
theorem completeDerived_homology_pow_annihilated (a : R) (X : ConcreteDerivedCategory R)
    (hX : IsComplete R a X) (i : ℤ) (g : R) (N : ℕ)
    (h : ∀ n,
      (∀ x : (complexPowerKoszulStage R a (DerivedCategory.Q.objPreimage X) n).homology i,
        g ^ N • x = 0) ∧
      (∀ x : (complexPowerKoszulStage R a (DerivedCategory.Q.objPreimage X) n).homology (i - 1),
        g ^ N • x = 0))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj X) :
    g ^ (2 * N) • x = 0 :=
  derived_homology_pow_annihilated_of_iso_homotopyLimit R
    (complexPowerKoszulStage R a (DerivedCategory.Q.objPreimage X))
    (complexPowerKoszulTransition R a (DerivedCategory.Q.objPreimage X))
    X (completeDerivedKoszulHomotopyLimitIso R a X hX) i g N h x

end SerrePositivity.DerivedCompletion
