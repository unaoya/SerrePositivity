module
public import SerrePositivity.DifferentialGraded.Perfect.RingBounded
public import SerrePositivity.DifferentialGraded.Perfect.Enhancement
public import SerrePositivity.DifferentialGraded.Category.Restriction
public import SerrePositivity.DifferentialGraded.Module.RingHomotopyComparison

/-! # 有限射影複体から主perfect dg enhancementへの実際のdg関手 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 有限射影複体の定数加群は主射影的perfect条件を満たす。 -/
lemma strictlyPerfectComplex_ringModule_perfectProjective (P : Complex A)
    (hP : strictlyPerfectComplex A P) :
    modulePerfectProjectiveOver A PUnit.{1} Set.univ (ringModule A P) :=
  ⟨strictlyPerfectComplex_ringModule_homotopicallyProjective A P hP,
    strictlyPerfectComplex_ringDerived_perfect A P hP⟩

/-- 対象を実際のringModuleへ、全Homを評価同型の逆へ送るdg比較。 -/
def strictPerfectDGComplexToPerfectDG :
    DGFunctor A (StrictPerfectDGComplex A) (PerfectDGModule A PUnit.{1}) :=
  (ringConstantDG A).restrict (strictlyPerfectComplex A)
    (modulePerfectProjectiveOver A PUnit.{1} Set.univ)
    (strictlyPerfectComplex_ringModule_perfectProjective A)

/-- 主dg包含との比較は元の全一対象加群へのdg関手との等式。 -/
lemma strictPerfectDGComplexToPerfectDG_comp_inclusion :
    DGFunctor.comp (strictPerfectDGComplexToPerfectDG A)
      (perfectDGModuleInclusion A PUnit.{1} Set.univ) =
    DGFunctor.comp (strictPerfectDGComplexInclusion A) (ringConstantDG A) :=
  (ringConstantDG A).restrict_comp_inclusion (strictlyPerfectComplex A)
    (modulePerfectProjectiveOver A PUnit.{1} Set.univ)
    (strictlyPerfectComplex_ringModule_perfectProjective A)

instance strictPerfectDGComplexToPerfectDGHomotopyFull :
    (strictPerfectDGComplexToPerfectDG A).onHomotopy.Full :=
  (strictPerfectDGComplexToPerfectDG A).onHomotopy_full_of_homIso (fun P N => by
    change IsIso (ringConstantHomIso A P.val N.val).inv
    infer_instance)

instance strictPerfectDGComplexToPerfectDGHomotopyFaithful :
    (strictPerfectDGComplexToPerfectDG A).onHomotopy.Faithful :=
  (strictPerfectDGComplexToPerfectDG A).onHomotopy_faithful_of_homIso (fun P N => by
    change IsIso (ringConstantHomIso A P.val N.val).inv
    infer_instance)

end SerrePositivity.DifferentialGraded
