module
public import SerrePositivity.DifferentialGraded.Derived.FunctorDerivedEquivalence

/-! # U16b：既存の導来擬同値と実際の随伴shift・三角構造

同値本体は既存dgFunctorDerivedEquivalenceを使い、順逆のshiftも既存の導来随伴のものを保つ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

local instance : (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance : (dgDerivedExtension A D E F).CommShift ℤ := dgDerivedExtensionCommShift A D E F

@[instance_reducible]
def quasiEquivalenceDerivedFunctorCommShift (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).functor.CommShift ℤ :=
  dgDerivedExtensionCommShift A D E F

@[instance_reducible]
def quasiEquivalenceDerivedInverseCommShift (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).inverse.CommShift ℤ :=
  dgDerivedRestrictionCommShift A D E F

attribute [local instance] quasiEquivalenceDerivedFunctorCommShift
  quasiEquivalenceDerivedInverseCommShift

lemma quasiEquivalenceDerivedCommShift (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).CommShift ℤ :=
  Equivalence.CommShift.mk' (dgFunctorDerivedEquivalence A D E F hF) ℤ
    (dgDerivedExtensionUnit_commShift A D E F)

lemma quasiEquivalenceDerivedIsTriangulated (hF : QuasiEquivalence F) :
    letI := quasiEquivalenceDerivedCommShift A D E F hF
    (dgFunctorDerivedEquivalence A D E F hF).IsTriangulated := by
  let := quasiEquivalenceDerivedCommShift A D E F hF
  exact Equivalence.IsTriangulated.mk' (dgFunctorDerivedEquivalence A D E F hF)
    (dgDerivedExtensionIsTriangulated A D E F)

/-- 同値の単位は既存の導来延長–制限の単位であり、そのshift整合性を保持する。 -/
lemma quasiEquivalenceDerivedUnitCommShift (hF : QuasiEquivalence F) :
    NatTrans.CommShift (dgFunctorDerivedEquivalence A D E F hF).unitIso.hom ℤ :=
  dgDerivedExtensionUnit_commShift A D E F

lemma quasiEquivalenceDerivedCounitCommShift (hF : QuasiEquivalence F) :
    NatTrans.CommShift (dgFunctorDerivedEquivalence A D E F hF).counitIso.hom ℤ :=
  dgDerivedExtensionCounit_commShift A D E F

end SerrePositivity.DifferentialGraded
