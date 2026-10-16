module
public import SerrePositivity.DifferentialGraded.Perfect.RingShiftComparison
public import SerrePositivity.DifferentialGraded.Category.ComplexHomotopyComparison

/-! # 実際のdg複体H⁰からの主導来比較と既存Qhの自然同型

閉零圏上の比較を境界商へ降ろす。ホモトピー圏の対象選択を比較の仮定にしない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 通常複体への閉零比較を戻して定数dg加群へ送ると、元の閉零dg関手と一致する。 -/
def complexClosedRingModuleIso :
    closedToComplex A ⋙ complexToRingModule A ≅ (ringConstantDG A).onClosed :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ForgetEnrichment.equiv (Complex A)
      (D := Complex A)).unitIso.symm (ringConstantDG A).onClosed ≪≫
    Functor.leftUnitor _

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 主dg関手のH⁰と主局所化の合成は、既存の通常Qhを経由する比較と自然同型。 -/
def complexHomotopyRingDerivedIso :
    (ringConstantDG A).onHomotopy ⋙ moduleHomotopyToDerivedClosed A PUnit.{1} ≅
      complexHomotopyComparison A ⋙ DerivedCategory.Qh ⋙ (ringDerivedEquivalence A).inverse := by
  let q := toHomotopy A (Complex A)
  let C := (ringConstantDG A).onClosed
  let L := moduleHomotopyToDerivedClosed A PUnit.{1}
  let Q := moduleToDerived A PUnit.{1}
  let J := (ringDerivedEquivalence A).inverse
  let E := closedToComplex A
  let α : q ⋙ ((ringConstantDG A).onHomotopy ⋙ L) ≅
      (E ⋙ DerivedCategory.Q) ⋙ J :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso ((ringConstantDG A).onHomotopy_fac)) L ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft C (moduleToHomotopyDerivedIso A PUnit.{1}) ≪≫
    Functor.isoWhiskerRight (complexClosedRingModuleIso A).symm Q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft E (ringComplexDerivedUnitNatIso A).symm ≪≫
    (Functor.associator _ _ _).symm
  let β : q ⋙ (complexHomotopyComparison A ⋙ DerivedCategory.Qh ⋙ J) ≅
      (E ⋙ DerivedCategory.Q) ⋙ J :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (complexHomotopyComparison_fac A)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft E ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)) J) ≪≫
    (Functor.associator _ _ _).symm
  exact CategoryTheory.Quotient.natIsoLift (boundaryRelation A (Complex A)) (α ≪≫ β.symm)

end SerrePositivity.DifferentialGraded
