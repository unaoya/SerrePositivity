module
public import SerrePositivity.DifferentialGraded.Derived.RingCoproducts

/-! # 導来余積と一対象環の比較の受入検査 -/
@[expose] public section
universe u v w
open CategoryTheory Limits SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (J : Type w) [Small.{u} J]

example : HasColimitsOfShape (Discrete J) (DerivedModuleCategory A D) := inferInstance

example (M : J → DerivedModuleCategory A D) : HasCoproduct M := inferInstance

#print axioms moduleProjectiveDerivedHomEquiv_precompose
#print axioms moduleProjectiveDerivedCofan
#print axioms moduleProjectiveDerivedCofanDesc
#print axioms moduleProjectiveDerivedCofanDesc_fac
#print axioms moduleProjectiveDerivedCoproduct_hom_ext
#print axioms moduleProjectiveDerivedCofanIsColimit
#print axioms moduleDerivedHasCoproductsOfShape
#print axioms ringDerivedEquivalencePreservesCoproducts
#print axioms ringDerivedInversePreservesCoproducts
#print axioms ringDerivedTargetHasCoproducts
#print axioms ringDerivedCoproductComparisonIsIso
