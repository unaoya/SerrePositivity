module
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-! # 導来三角構造と比較の受入検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
example (x : D) : (moduleDerivedEvaluation A D x).IsTriangulated := inferInstance
example : (ringDerivedEquivalence A).functor.IsTriangulated := inferInstance
example : (ringDerivedEquivalence A).inverse.IsTriangulated := inferInstance
#print axioms mapTriangleTripleSquareIso
#print axioms moduleDerivedEvaluationHomotopyFacIso
#print axioms moduleDerivedEvaluationHomotopyFacCommShift
#print axioms moduleDerivedConeTriangleEvaluationIso
#print axioms moduleDerivedEvaluationIsTriangulated
#print axioms ringDerivedEquivalenceIsTriangulated
#print axioms ringDerivedEquivalenceInverseCommShift
#print axioms ringDerivedEquivalenceCounitCommShift
#print axioms ringDerivedEquivalenceInverseIsTriangulated
