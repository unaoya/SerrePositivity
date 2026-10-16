module
public import SerrePositivity.DifferentialGraded.Category.ComplexHomotopyComparison
public import Mathlib.Data.ZMod.Basic

/-! # 主dg複体のH⁰と既存ホモトピー商の線形比較 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example : (complexHomotopyComparison A).IsEquivalence := inferInstance
example : (complexHomotopyComparison A).Linear A := inferInstance
example : (complexHomotopyEquivalence A).inverse.Linear A := inferInstance
example : (complexHomotopyEquivalence A).inverse.Additive := inferInstance
example (P Q : Complex A) (f : P ⟶ Q) :
    (complexHomotopyComparison A).map ((toHomotopy A (Complex A)).map
      ((complexClosedHomEquiv A P Q).symm f)) =
      (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).map f := by
  change (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).map
    ((complexClosedHomEquiv A P Q) ((complexClosedHomEquiv A P Q).symm f)) = _
  rw [Equiv.apply_symm_apply]
example : (complexHomotopyEquivalence (ZMod 2)).inverse.Linear (ZMod 2) := inferInstance

#print axioms closedToComplexLinear
#print axioms complexHomotopyComparison
#print axioms complexHomotopyComparison_fac
#print axioms complexHomotopyComparisonFull
#print axioms complexHomotopyComparisonFaithful
#print axioms complexHomotopyComparisonEssSurj
#print axioms complexHomotopyComparisonIsEquivalence
#print axioms complexHomotopyEquivalence
#print axioms complexHomotopyComparisonAdditive
#print axioms complexHomotopyComparisonLinear
#print axioms complexHomotopyEquivalenceFunctorLinear
#print axioms complexHomotopyEquivalenceFunctorAdditive
