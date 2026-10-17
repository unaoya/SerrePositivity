module
public import SerrePositivity.DifferentialGraded.Module.RestrictionEnriched
public import SerrePositivity.DifferentialGraded.Derived.Restriction
public import SerrePositivity.DifferentialGraded.Endomorphism.ConeTriangleComparison
public import SerrePositivity.DifferentialGraded.Derived.Shift

/-! # 導来制限の全Homモデルと整合的整数shift -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgDerivedRestriction_enriched_fac :
    moduleToDerived A E ⋙ dgDerivedRestriction A D E F =
      (dgModuleRestriction A D E F.op).onClosed ⋙ moduleToDerived A D := by
  rw [dgModuleRestriction_onClosed_eq]
  exact dgDerivedRestriction_fac A D E F

instance dgDerivedRestriction_enriched_lifting :
    Localization.Lifting (moduleToDerived A E) (moduleQuasiIso A E)
      ((dgModuleRestriction A D E F.op).onClosed ⋙ moduleToDerived A D)
      (dgDerivedRestriction A D E F) := ⟨eqToIso (dgDerivedRestriction_enriched_fac A D E F)⟩

/-- U14の全dg関手用shift比較を局所化し、既存の導来制限に与える。 -/
@[instance_reducible]
def dgDerivedRestrictionCommShift : (dgDerivedRestriction A D E F).CommShift ℤ := by
  letI := dgModuleFunctorCommShift A E D (dgModuleRestriction A D E F.op)
  exact Functor.commShiftOfLocalization (moduleToDerived A E) (moduleQuasiIso A E) ℤ
    ((dgModuleRestriction A D E F.op).onClosed ⋙ moduleToDerived A D)
    (dgDerivedRestriction A D E F)

section
local instance : (dgModuleRestriction A D E F.op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A E D (dgModuleRestriction A D E F.op)
local instance : (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F

lemma dgDerivedRestrictionFac_commShift :
    NatTrans.CommShift (eqToIso (dgDerivedRestriction_enriched_fac A D E F)).hom ℤ := by
  change NatTrans.CommShift
    (Localization.Lifting.iso (moduleToDerived A E) (moduleQuasiIso A E)
      ((dgModuleRestriction A D E F.op).onClosed ⋙ moduleToDerived A D)
      (dgDerivedRestriction A D E F)).hom ℤ
  exact NatTrans.commShift_iso_hom_of_localization (moduleToDerived A E) (moduleQuasiIso A E) ℤ
    ((dgModuleRestriction A D E F.op).onClosed ⋙ moduleToDerived A D)
    (dgDerivedRestriction A D E F)
end
end SerrePositivity.DifferentialGraded
