module
public import SerrePositivity.DifferentialGraded.Module.GradedSplitElements
public import SerrePositivity.DifferentialGraded.Module.Semifree.Basic

/-! # U10b4b：全次数分裂から得られるHom制限の全射性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D) (q : ℤ) :
    Function.Surjective ((eHomWhiskerRight (Complex A) f T).f q) :=
  s.homRestriction_surjective T q

example {M : ModuleCategory A D} (F : ModuleSemifreeFiltration A D M)
    (T : ModuleCategory A D) (n : ℕ) (q : ℤ) :
    Function.Surjective ((eHomWhiskerRight (Complex A) (F.transition n) T).f q) :=
  (F.split n).homRestriction_surjective T q

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms moduleHomForward_π
#print axioms moduleHomWhiskerRight_apply_π
#print axioms moduleGradedNaturalElement
#print axioms moduleGradedNaturalElement_π
#print axioms ModuleGradedSplit.retractionElement
#print axioms ModuleGradedSplit.sectionElement
#print axioms ModuleGradedSplit.retractionElement_π
#print axioms ModuleGradedSplit.sectionElement_π
#print axioms ModuleGradedSplit.homRestrictionSection
#print axioms ModuleGradedSplit.homRestrictionSection_π
#print axioms ModuleGradedSplit.homRestriction_section
#print axioms ModuleGradedSplit.homRestriction_surjective
