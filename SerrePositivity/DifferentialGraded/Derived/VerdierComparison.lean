module
public import SerrePositivity.DifferentialGraded.Derived.Triangulated

/-! # 主導来加群圏とacyclic部分圏による標準Verdier商の三角同値 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定準同型の主局所化と、acyclic部分圏の標準Verdier局所化との同値。 -/
def moduleDerivedVerdierEquivalence :
    DerivedModuleCategory A D ≌ (moduleHomotopyAcyclic A D).trW.Localization :=
  Localization.uniq (moduleHomotopyToDerivedClosed A D)
    (moduleHomotopyAcyclic A D).trW.Q (moduleHomotopyAcyclic A D).trW

def moduleDerivedVerdierComparisonIso :
    moduleHomotopyToDerivedClosed A D ⋙ (moduleDerivedVerdierEquivalence A D).functor ≅
      (moduleHomotopyAcyclic A D).trW.Q :=
  Localization.compUniqFunctor (moduleHomotopyToDerivedClosed A D)
    (moduleHomotopyAcyclic A D).trW.Q (moduleHomotopyAcyclic A D).trW

instance moduleDerivedVerdierLifting :
    Localization.Lifting (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)
      (moduleHomotopyAcyclic A D).trW.Q (moduleDerivedVerdierEquivalence A D).functor :=
  ⟨moduleDerivedVerdierComparisonIso A D⟩

instance moduleDerivedVerdierCommShift :
    (moduleDerivedVerdierEquivalence A D).functor.CommShift ℤ :=
  Functor.commShiftOfLocalization (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D) ℤ
    (moduleHomotopyAcyclic A D).trW.Q (moduleDerivedVerdierEquivalence A D).functor

instance moduleDerivedVerdierComparisonCommShift :
    NatTrans.CommShift (moduleDerivedVerdierComparisonIso A D).hom ℤ := by
  change NatTrans.CommShift
    (Localization.Lifting.iso (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)
      (moduleHomotopyAcyclic A D).trW.Q (moduleDerivedVerdierEquivalence A D).functor).hom ℤ
  exact NatTrans.commShift_iso_hom_of_localization
    (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D) ℤ
    (moduleHomotopyAcyclic A D).trW.Q (moduleDerivedVerdierEquivalence A D).functor

instance moduleDerivedVerdierIsTriangulated :
    (moduleDerivedVerdierEquivalence A D).functor.IsTriangulated :=
  Functor.isTriangulated_of_precomp_iso
    (F := moduleHomotopyToDerivedClosed A D) (G := (moduleDerivedVerdierEquivalence A D).functor)
    (moduleDerivedVerdierComparisonIso A D)

instance moduleDerivedVerdierInverseCommShift :
    (moduleDerivedVerdierEquivalence A D).inverse.CommShift ℤ :=
  Functor.CommShift.ofComp (moduleDerivedVerdierEquivalence A D).counitIso ℤ

instance moduleDerivedVerdierCounitCommShift :
    NatTrans.CommShift (moduleDerivedVerdierEquivalence A D).counitIso.hom ℤ :=
  Functor.CommShift.ofComp_compatibility (moduleDerivedVerdierEquivalence A D).counitIso ℤ

instance moduleDerivedVerdierInverseIsTriangulated :
    (moduleDerivedVerdierEquivalence A D).inverse.IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right (moduleDerivedVerdierEquivalence A D).counitIso).2
    inferInstance

end SerrePositivity.DifferentialGraded
