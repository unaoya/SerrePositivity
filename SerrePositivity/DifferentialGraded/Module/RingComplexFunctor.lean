module
public import SerrePositivity.DifferentialGraded.Module.RingDGComparison
public import SerrePositivity.DifferentialGraded.Category.ComplexHomotopyComparison

/-! # 通常の非有界複体から実際の一対象Aの右dg加群への関手 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 通常のchain mapを閉零射へ戻して、実際のringConstantDGを適用する。 -/
def complexToRingModule : Complex A ⥤ ModuleCategory A PUnit.{1} :=
  ForgetEnrichment.equivInverse (Complex A) (Complex A) ⋙ (ringConstantDG A).onClosed

instance complexToRingModuleAdditive : (complexToRingModule A).Additive := by
  let e : ClosedCategory A (Complex A) ≌ Complex A := ForgetEnrichment.equiv (Complex A)
  have : e.functor.Additive := closedToComplexAdditive (A := A)
  have : (ForgetEnrichment.equivInverse (Complex A) (Complex A)).Additive :=
    show e.inverse.Additive from inferInstance
  dsimp [complexToRingModule]
  infer_instance

end SerrePositivity.DifferentialGraded
