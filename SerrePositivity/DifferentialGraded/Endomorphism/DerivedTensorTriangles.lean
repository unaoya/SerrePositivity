module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedTriangleComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedAdjunction
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # 実際の再構成導来tensorと随伴の整合的shift・三角性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)
variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

local instance : (endomorphismDerivedHom A D E hE).CommShift ℤ :=
  endomorphismDerivedHomCommShift A D E hE
local instance : (endomorphismDerivedHom A D E hE).IsTriangulated :=
  endomorphismDerivedHomIsTriangulated A D E hE

/-- 導来随伴から実際の左関手へ運ぶ整合的shift。 -/
@[instance_reducible]
def endomorphismDerivedTensorCommShift : (endomorphismDerivedTensor A D E).CommShift ℤ :=
  (endomorphismDerivedAdjunction A D E hE).leftAdjointCommShift ℤ

lemma endomorphismDerivedAdjunction_commShift :
    letI := endomorphismDerivedTensorCommShift A D E hE
    (endomorphismDerivedAdjunction A D E hE).CommShift ℤ :=
  (endomorphismDerivedAdjunction A D E hE).commShift_of_rightAdjoint ℤ

lemma endomorphismDerivedUnit_commShift :
    letI := endomorphismDerivedTensorCommShift A D E hE
    NatTrans.CommShift (endomorphismDerivedUnit A D E hE) ℤ := by
  let := endomorphismDerivedTensorCommShift A D E hE
  let := endomorphismDerivedAdjunction_commShift A D E hE
  unfold endomorphismDerivedUnit
  infer_instance

lemma endomorphismDerivedCounit_commShift :
    letI := endomorphismDerivedTensorCommShift A D E hE
    NatTrans.CommShift (endomorphismDerivedCounit A D E hE) ℤ := by
  let := endomorphismDerivedTensorCommShift A D E hE
  let := endomorphismDerivedAdjunction_commShift A D E hE
  unfold endomorphismDerivedCounit
  infer_instance

lemma endomorphismDerivedTensorIsTriangulated :
    letI := endomorphismDerivedTensorCommShift A D E hE
    (endomorphismDerivedTensor A D E).IsTriangulated := by
  let := endomorphismDerivedTensorCommShift A D E hE
  let := endomorphismDerivedAdjunction_commShift A D E hE
  exact (endomorphismDerivedAdjunction A D E hE).isTriangulated_leftAdjoint

end SerrePositivity.DifferentialGraded
