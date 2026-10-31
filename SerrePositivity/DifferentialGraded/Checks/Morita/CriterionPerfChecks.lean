module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerf
public import SerrePositivity.DifferentialGraded.Morita.CoherenceIdentity
public import Mathlib.Data.ZMod.Basic

@[expose] public section
noncomputable section
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
universe u v

/-- 恒等 kernel の実作用との比較から三条件を再現する。局所平坦性は不要。 -/
example (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D] :
    CriterionPerfConditions A D D (kernelIdentity A D) := by
  let W : CriterionPerfEquivalenceWitness A D D (kernelIdentity A D) :=
    ⟨CategoryTheory.Equivalence.refl,
      isoWhiskerLeft (perfectModuleInclusion A D Set.univ) (kernelIdentityIso A D)⟩
  exact W.conditions A D D (kernelIdentity A D)

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (K : Kernel (ZMod 2) D D) :
    CriterionPerfConditions (ZMod 2) D D K ↔
      Nonempty (CriterionPerfEquivalenceWitness (ZMod 2) D D K) :=
  criterionPerfMorita_iff (ZMod 2) D D K

#print axioms criterionPerfEquivalenceOfConditions
#print axioms CriterionPerfEquivalenceWitness.fullHomQuasiIso
#print axioms CriterionPerfEquivalenceWitness.conditions
#print axioms criterionPerfMorita_iff
#print axioms criterionPerfAction_isEquivalence_iff
end SerrePositivity.DifferentialGraded.Morita
