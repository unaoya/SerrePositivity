module
public import SerrePositivity.DifferentialGraded.Perfect.RingKaroubiFactors
public import Mathlib.Data.ZMod.Basic

/-! # Karoubi実現のfactor・導来比較・三角形比較の整合性の監査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Idempotents
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example : NatTrans.CommShift (ringPerfectKaroubiRealization_fac A).hom ℤ := inferInstance
example : NatTrans.CommShift (ringPerfectKaroubiRealizationDerivedIso A).hom ℤ := inferInstance
example : (toKaroubi (SerrePositivity.PerfectHomotopy A)).mapTriangle ⋙
    (ringPerfectKaroubiRealization A).mapTriangle ≅
      (perfectHomotopyToDGPerfect A).mapTriangle := ringPerfectKaroubiRealizationTriangleIso A
example : NatTrans.CommShift (ringPerfectKaroubiRealization_fac (ZMod 2)).hom ℤ := inferInstance

#print axioms equivalence_map_inverse_then_unit
#print axioms equivalenceExtension_factor_whisker
#print axioms ringPerfectKaroubi_fac_whisker
#print axioms ringPerfectKaroubiRealizationFacCommShift
#print axioms ringPerfectKaroubiRealizationTriangleIso
#print axioms ringPerfectKaroubiRealizationDerivedIso
#print axioms ringPerfectKaroubiRealizationDerivedIsoCommShift
