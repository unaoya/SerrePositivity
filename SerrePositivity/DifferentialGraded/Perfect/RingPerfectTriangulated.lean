module
public import SerrePositivity.DifferentialGraded.Perfect.RingPerfectComparison
public import SerrePositivity.DifferentialGraded.Perfect.RingHomotopyDerivedComparison

/-! # 既存PerfectHomotopyから主Perfへの比較のshift・三角整合性

既存の通常Qhを通る比較との自然同型で構造を運び、主Perf包含で反映する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]
local instance : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

local instance : (perfectModuleInclusion A PUnit.{1} Set.univ).Full := by
  dsimp [perfectModuleInclusion]
  infer_instance

local instance : (perfectModuleInclusion A PUnit.{1} Set.univ).Faithful := by
  dsimp [perfectModuleInclusion]
  infer_instance

/-- 有限射影dg複体の主導来比較と既存Qhによる比較の自然同型。 -/
def strictPerfectDGComplexDerivedCanonicalIso :
    strictPerfectDGComplexToDerived A ≅ strictPerfectDGComplexToHomotopy A ⋙
      DerivedCategory.Qh ⋙ (ringDerivedEquivalence A).inverse :=
  Functor.isoWhiskerRight
      (eqToIso (DGFunctor.onHomotopy_comp (strictPerfectDGComplexInclusion A)
        (ringConstantDG A))) (moduleHomotopyToDerivedClosed A PUnit.{1}) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (strictPerfectDGComplexInclusion A).onHomotopy
      (complexHomotopyRingDerivedIso A) ≪≫
    (Functor.associator _ _ _).symm

/-- 既存PerfectHomotopyからの主導来比較を、元の包含・Qhと同定する。 -/
def perfectHomotopyToDGDerivedCanonicalIso :
    perfectHomotopyToDGDerived A ≅ perfectHomotopyInclusion A ⋙
      DerivedCategory.Qh ⋙ (ringDerivedEquivalence A).inverse := by
  let E := strictPerfectDGComplexHomotopyEquivalence A
  let I := perfectHomotopyInclusion A
  let h : E.inverse ⋙ strictPerfectDGComplexToHomotopy A ≅ I :=
    Functor.isoWhiskerLeft E.inverse (strictPerfectDGComplexToPerfectCompInclusion A).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.counitIso I ≪≫ Functor.leftUnitor I
  exact Functor.isoWhiskerLeft E.inverse (strictPerfectDGComplexDerivedCanonicalIso A) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight h _

instance perfectHomotopyToDGDerivedCommShift : (perfectHomotopyToDGDerived A).CommShift ℤ :=
  Functor.CommShift.ofIso (perfectHomotopyToDGDerivedCanonicalIso A).symm ℤ

instance perfectHomotopyToDGDerivedCanonicalIsoCommShift :
    NatTrans.CommShift (perfectHomotopyToDGDerivedCanonicalIso A).hom ℤ := by
  have : NatTrans.CommShift (perfectHomotopyToDGDerivedCanonicalIso A).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (perfectHomotopyToDGDerivedCanonicalIso A).symm ℤ
  exact NatTrans.CommShift.of_iso_inv (perfectHomotopyToDGDerivedCanonicalIso A).symm ℤ

instance perfectHomotopyToDGDerivedIsTriangulated :
    (perfectHomotopyToDGDerived A).IsTriangulated :=
  Functor.isTriangulated_of_iso (perfectHomotopyToDGDerivedCanonicalIso A).symm

instance perfectHomotopyToDGPerfectCommShift : (perfectHomotopyToDGPerfect A).CommShift ℤ :=
  Functor.CommShift.ofComp (perfectHomotopyToDGPerfectCompInclusion A) ℤ

instance perfectHomotopyToDGPerfectCompInclusionCommShift :
    NatTrans.CommShift (perfectHomotopyToDGPerfectCompInclusion A).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (perfectHomotopyToDGPerfectCompInclusion A) ℤ

instance perfectHomotopyToDGPerfectIsTriangulated :
    (perfectHomotopyToDGPerfect A).IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right (perfectHomotopyToDGPerfectCompInclusion A)).2
    inferInstance

end SerrePositivity.DifferentialGraded
