module
public import SerrePositivity.DifferentialGraded.Perfect.StrictComplexProjective
public import SerrePositivity.DifferentialGraded.Module.RingHomotopyComparison
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveLocalizationHom

/-! # 有限射影複体のH⁰から主dg加群導来圏への完全忠実な比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 有限射影複体を実際の一対象Aのdg加群へ送るdg関手。 -/
def strictPerfectDGComplexToRingModule :
    DGFunctor A (StrictPerfectDGComplex A) (RightModule A PUnit.{1}) :=
  DGFunctor.comp (strictPerfectDGComplexInclusion A) (ringConstantDG A)

instance strictPerfectDGComplexToRingModuleHomotopyFull :
    (strictPerfectDGComplexToRingModule A).onHomotopy.Full := by
  rw [strictPerfectDGComplexToRingModule, DGFunctor.onHomotopy_comp]
  infer_instance

instance strictPerfectDGComplexToRingModuleHomotopyFaithful :
    (strictPerfectDGComplexToRingModule A).onHomotopy.Faithful := by
  rw [strictPerfectDGComplexToRingModule, DGFunctor.onHomotopy_comp]
  infer_instance

/-- 実際のdg比較のH⁰に、既存の準同型局所化を合成する。 -/
def strictPerfectDGComplexToDerived : HomotopyCategory A (StrictPerfectDGComplex A) ⥤
    DerivedModuleCategory A PUnit.{1} :=
  (strictPerfectDGComplexToRingModule A).onHomotopy ⋙ moduleHomotopyToDerivedClosed A PUnit.{1}

instance strictPerfectDGComplexToDerivedFull : (strictPerfectDGComplexToDerived A).Full where
  map_surjective {X Y} f := by
    let M : StrictPerfectDGComplex A := ForgetEnrichment.to (Complex A) X.as
    let N : ModuleCategory A PUnit.{1} := ForgetEnrichment.of (Complex A) (ringModule A M.val)
    obtain ⟨g, hg⟩ := (moduleProjectiveLocalization_map_bijective A PUnit.{1}
      (P := N) (strictlyPerfectComplex_ringModule_homotopicallyProjective A M.val M.property)
      ((strictPerfectDGComplexToRingModule A).onHomotopy.obj Y)).2 f
    obtain ⟨h, hh⟩ := (strictPerfectDGComplexToRingModule A).onHomotopy.map_surjective g
    refine ⟨h, ?_⟩
    change (moduleHomotopyToDerivedClosed A PUnit.{1}).map
      ((strictPerfectDGComplexToRingModule A).onHomotopy.map h) = f
    rw [hh]
    exact hg

instance strictPerfectDGComplexToDerivedFaithful :
    (strictPerfectDGComplexToDerived A).Faithful where
  map_injective {X Y} f g h := by
    let M : StrictPerfectDGComplex A := ForgetEnrichment.to (Complex A) X.as
    let N : ModuleCategory A PUnit.{1} := ForgetEnrichment.of (Complex A) (ringModule A M.val)
    apply (strictPerfectDGComplexToRingModule A).onHomotopy.map_injective
    exact (moduleProjectiveLocalization_map_bijective A PUnit.{1}
      (P := N) (strictlyPerfectComplex_ringModule_homotopicallyProjective A M.val M.property)
      ((strictPerfectDGComplexToRingModule A).onHomotopy.obj Y)).1 h

end SerrePositivity.DifferentialGraded
