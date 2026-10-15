module
public import SerrePositivity.DifferentialGraded.Derived.VerdierComparison

/-! # 導来三角構造と比較の受入検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example : (moduleDerivedVerdierEquivalence A D).functor.IsTriangulated := inferInstance
example : (moduleDerivedVerdierEquivalence A D).inverse.IsTriangulated := inferInstance
example : NatTrans.CommShift (moduleDerivedVerdierComparisonIso A D).hom ℤ := inferInstance
#print axioms moduleDerivedVerdierEquivalence
#print axioms moduleDerivedVerdierComparisonIso
#print axioms moduleDerivedVerdierLifting
#print axioms moduleDerivedVerdierCommShift
#print axioms moduleDerivedVerdierComparisonCommShift
#print axioms moduleDerivedVerdierIsTriangulated
#print axioms moduleDerivedVerdierInverseCommShift
#print axioms moduleDerivedVerdierCounitCommShift
#print axioms moduleDerivedVerdierInverseIsTriangulated
