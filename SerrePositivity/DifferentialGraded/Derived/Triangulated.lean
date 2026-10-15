module
public import SerrePositivity.DifferentialGraded.Module.Triangulated
public import SerrePositivity.DifferentialGraded.Module.AcyclicTriangulated
public import SerrePositivity.DifferentialGraded.Derived.HomotopyShift
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive

/-! # 指定された導来加群圏の三角構造とVerdier局所化 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleHomotopyQuasiIsoLeftFractions :
    (moduleHomotopyQuasiIso A D).HasLeftCalculusOfFractions := by
  rw [← moduleHomotopyAcyclic_trW_eq A D]
  infer_instance

instance moduleHomotopyQuasiIsoRightFractions :
    (moduleHomotopyQuasiIso A D).HasRightCalculusOfFractions := by
  rw [← moduleHomotopyAcyclic_trW_eq A D]
  infer_instance

instance moduleHomotopyQuasiIsoTriangulation :
    (moduleHomotopyQuasiIso A D).IsCompatibleWithTriangulation := by
  rw [← moduleHomotopyAcyclic_trW_eq A D]
  infer_instance

instance moduleDerivedPreadditive : Preadditive (DerivedModuleCategory A D) :=
  Localization.preadditive (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)

instance moduleHomotopyToDerivedClosedAdditive : (moduleHomotopyToDerivedClosed A D).Additive :=
  Localization.functor_additive (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)

instance moduleDerivedHasZeroObject : HasZeroObject (DerivedModuleCategory A D) :=
  (moduleHomotopyToDerivedClosed A D).hasZeroObject_of_additive

instance moduleDerivedShiftAdditive (s : ℤ) :
    (shiftFunctor (DerivedModuleCategory A D) s).Additive := by
  rw [Localization.functor_additive_iff
    (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)]
  exact Functor.additive_of_iso ((moduleHomotopyToDerivedClosed A D).commShiftIso s)

/-- U9で構成した主導来圏そのものにVerdier局所化の三角構造を入れる。 -/
instance moduleDerivedPretriangulated : Pretriangulated (DerivedModuleCategory A D) :=
  Triangulated.Localization.pretriangulated
    (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)

instance moduleHomotopyToDerivedClosedIsTriangulated :
    (moduleHomotopyToDerivedClosed A D).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor
    (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)

instance moduleDerivedIsTriangulated : IsTriangulated (DerivedModuleCategory A D) :=
  Triangulated.Localization.isTriangulated
    (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)

instance moduleHomotopyToDerivedClosedArrowEssSurj :
    (moduleHomotopyToDerivedClosed A D).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)

/-- 主導来圏は、acyclic部分圏のVerdier射を局所化している。 -/
instance moduleHomotopyToDerivedVerdierIsLocalization :
    (moduleHomotopyToDerivedClosed A D).IsLocalization (moduleHomotopyAcyclic A D).trW := by
  rw [moduleHomotopyAcyclic_trW_eq A D]
  infer_instance

lemma moduleDerived_distinguished_iff (T : Triangle (DerivedModuleCategory A D)) :
    T ∈ distTriang (DerivedModuleCategory A D) ↔
      T ∈ (moduleHomotopyToDerivedClosed A D).essImageDistTriang := Iff.rfl

instance moduleHomotopyToDerivedIsTriangulated :
    (moduleHomotopyToDerived A D).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor
    (moduleHomotopyToDerived A D) (moduleHomotopyQuasiIso A D)

instance moduleHomotopyToDerivedArrowEssSurj :
    (moduleHomotopyToDerived A D).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow (moduleHomotopyToDerived A D) (moduleHomotopyQuasiIso A D)

instance moduleDerivedHomotopyInverseIsTriangulated :
    (moduleDerivedHomotopyEquivalence A D).inverse.IsTriangulated := by
  let : (moduleHomotopyToDerived A D ⋙
      (moduleDerivedHomotopyEquivalence A D).inverse).IsTriangulated :=
    moduleHomotopyToDerivedClosedIsTriangulated A D
  exact Functor.isTriangulated_of_precomp (moduleHomotopyToDerived A D)
    (moduleDerivedHomotopyEquivalence A D).inverse

end SerrePositivity.DifferentialGraded
