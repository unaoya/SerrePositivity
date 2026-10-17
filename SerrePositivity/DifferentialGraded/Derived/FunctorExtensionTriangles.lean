module
public import SerrePositivity.DifferentialGraded.Derived.RestrictionTriangles
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # graph導来随伴に整合する整数shiftと三角性 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

local instance : (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance : (dgDerivedRestriction A D E F).IsTriangulated :=
  dgDerivedRestrictionIsTriangulated A D E F
local instance : (dgDerivedRestriction A D E F).Additive := dgDerivedRestriction_additive A D E F

/-- 実際の導来随伴から左関手へ運ぶ、随伴と整合するshift。 -/
@[instance_reducible]
def dgDerivedExtensionCommShift : (dgDerivedExtension A D E F).CommShift ℤ :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).leftAdjointCommShift ℤ

lemma dgDerivedExtensionRestrictionAdjunction_commShift :
    letI := dgDerivedExtensionCommShift A D E F
    (dgDerivedExtensionRestrictionAdjunction A D E F).CommShift ℤ :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).commShift_of_rightAdjoint ℤ

lemma dgDerivedExtensionUnit_commShift :
    letI := dgDerivedExtensionCommShift A D E F
    NatTrans.CommShift (dgDerivedExtensionUnit A D E F) ℤ := by
  let := dgDerivedExtensionCommShift A D E F
  let := dgDerivedExtensionRestrictionAdjunction_commShift A D E F
  unfold dgDerivedExtensionUnit
  infer_instance

lemma dgDerivedExtensionCounit_commShift :
    letI := dgDerivedExtensionCommShift A D E F
    NatTrans.CommShift (dgDerivedExtensionCounit A D E F) ℤ := by
  let := dgDerivedExtensionCommShift A D E F
  let := dgDerivedExtensionRestrictionAdjunction_commShift A D E F
  unfold dgDerivedExtensionCounit
  infer_instance

lemma dgDerivedExtensionIsTriangulated :
    letI := dgDerivedExtensionCommShift A D E F
    (dgDerivedExtension A D E F).IsTriangulated := by
  let := dgDerivedExtensionCommShift A D E F
  let := dgDerivedExtensionRestrictionAdjunction_commShift A D E F
  exact (dgDerivedExtensionRestrictionAdjunction A D E F).isTriangulated_leftAdjoint

lemma dgDerivedExtension_additive : (dgDerivedExtension A D E F).Additive :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).left_adjoint_additive

end SerrePositivity.DifferentialGraded
