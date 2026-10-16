module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Module
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Extension closure in the category of derived-complete modules -/

@[expose] public section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory

/-- Extension closure of I-annihilated objects inside actual derived-a-complete modules. -/
def CompleteIdealExtensionClosed (B : Type u) [CommRing B] (a : B) (I : Ideal B) : Prop :=
  ∀ S : ShortComplex (ModuleCat.{u} B), S.ShortExact →
    IsModuleComplete B a S.X₁ → IsModuleComplete B a S.X₂ → IsModuleComplete B a S.X₃ →
    I ≤ Module.annihilator B S.X₁ → I ≤ Module.annihilator B S.X₃ →
      I ≤ Module.annihilator B S.X₂


end SerrePositivity.DerivedCompletion
