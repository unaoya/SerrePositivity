module
public import SerrePositivity.DifferentialGraded.Perfect.StrictComplexDerived
public import SerrePositivity.DifferentialGraded.Perfect.StrictComplexEnhancementLinear
public import SerrePositivity.DifferentialGraded.Derived.HomotopyLinear

/-! # 既存PerfectHomotopyから主dg加群導来圏へのA線形完全忠実関手 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

instance strictPerfectDGComplexToDerivedAdditive :
    (strictPerfectDGComplexToDerived A).Additive := by
  dsimp [strictPerfectDGComplexToDerived]
  infer_instance

instance strictPerfectDGComplexToDerivedLinear : (strictPerfectDGComplexToDerived A).Linear A := by
  dsimp [strictPerfectDGComplexToDerived]
  infer_instance

/-- 既存PerfectHomotopyを主dg enhancement経由で指定導来圏へ送る。 -/
def perfectHomotopyToDGDerived : PerfectHomotopy A ⥤ DerivedModuleCategory A PUnit.{1} :=
  (strictPerfectDGComplexHomotopyEquivalence A).inverse ⋙ strictPerfectDGComplexToDerived A

instance perfectHomotopyToDGDerivedFull : (perfectHomotopyToDGDerived A).Full := by
  dsimp [perfectHomotopyToDGDerived]
  infer_instance

instance perfectHomotopyToDGDerivedFaithful : (perfectHomotopyToDGDerived A).Faithful := by
  dsimp [perfectHomotopyToDGDerived]
  infer_instance

instance perfectHomotopyToDGDerivedAdditive : (perfectHomotopyToDGDerived A).Additive := by
  dsimp [perfectHomotopyToDGDerived]
  infer_instance

instance perfectHomotopyToDGDerivedLinear : (perfectHomotopyToDGDerived A).Linear A := by
  dsimp [perfectHomotopyToDGDerived]
  infer_instance

/-- 既存perfectへのH⁰比較を経由しても、実際の一対象dg加群による主導来比較と一致する。 -/
def strictPerfectDGComplexToPerfectCompDerived :
    strictPerfectDGComplexToPerfect A ⋙ perfectHomotopyToDGDerived A ≅
      strictPerfectDGComplexToDerived A :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (strictPerfectDGComplexHomotopyEquivalence A).unitIso.symm _ ≪≫
    Functor.leftUnitor _

end SerrePositivity.DifferentialGraded
