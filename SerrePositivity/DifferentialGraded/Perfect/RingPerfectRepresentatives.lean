module
public import SerrePositivity.DifferentialGraded.Perfect.RingRetractFiniteRepresentative

/-! # 一対象Aの主Perfの全対象の有界有限射影代表 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]
local instance : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

def ringModule_complexDerivedIso (M : ModuleCategory A PUnit.{1}) :
    (moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj
        ((moduleEvaluation A PUnit.{1} PUnit.unit).obj M)) ≅
      (moduleToDerived A PUnit.{1}).obj M :=
  eqToIso (congrArg
    (fun N => (moduleToDerived A PUnit.{1}).obj (ForgetEnrichment.of (Complex A) N))
    (ringModule_recover A (ForgetEnrichment.to (Complex A) M)))

lemma ringModuleDerivedRetract_finiteProjective (P : Complex A)
    (hP : strictlyPerfectComplex A P) {X : DerivedModuleCategory A PUnit.{1}}
    (r : Retract X ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P))) :
    ∃ K : Complex A, strictlyPerfectComplex A K ∧
      Nonempty ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj K) ≅ X) := by
  let E := ringDerivedEquivalence A
  let eP : E.functor.obj ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P)) ≅
      DerivedCategory.Q.obj P := (complexToRingModuleDerivedEvaluationIso A).app P
  obtain ⟨K, hK, ⟨eK⟩⟩ := ringDerivedRetract_finiteProjective A P hP
    ((r.map E.functor).trans (Retract.ofIso eP))
  let e : E.functor.obj ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj K)) ≅
      E.functor.obj X := (complexToRingModuleDerivedEvaluationIso A).app K ≪≫ eK
  exact ⟨K, hK, ⟨(Functor.FullyFaithful.ofFullyFaithful E.functor).preimageIso e⟩⟩

lemma modulePerfect_ring_has_strictlyPerfectRepresentative
    {X : DerivedModuleCategory A PUnit.{1}} (hX : modulePerfect A PUnit.{1} X) :
    ∃ K : Complex A, strictlyPerfectComplex A K ∧
      Nonempty ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj K) ≅ X) := by
  obtain ⟨M, hM, ⟨r⟩⟩ := (modulePerfect_iff A PUnit.{1} X).1 hX
  let P := (moduleEvaluation A PUnit.{1} PUnit.unit).obj M
  have hP : strictlyPerfectComplex A P := moduleFiniteCell_ringEvaluation_strictlyPerfect A hM
  exact ringModuleDerivedRetract_finiteProjective A P hP
    (r.trans (Retract.ofIso (ringModule_complexDerivedIso A M).symm))

end SerrePositivity.DifferentialGraded
