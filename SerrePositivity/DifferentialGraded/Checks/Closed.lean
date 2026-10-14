module
public import SerrePositivity.DifferentialGraded.Complexes.Closed
public import Mathlib.Data.ZMod.Basic

/-! # U4 tensor–Hom の受入検査と公理監査 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A]
example : MonoidalClosed (Complex A) := inferInstance
example : MonoidalClosed (Complex (ZMod 2)) := inferInstance
example (P Q : Complex A) : P ⊗ Q = SerrePositivity.cochainTensor P Q := rfl
example (P T : Complex A) : (ihom P).obj T = CochainComplex.linearHomComplex A P T := rfl
example (P Q T : Complex A) :
    (SerrePositivity.cochainTensor P Q ⟶ T) ≃ (Q ⟶ CochainComplex.linearHomComplex A P T) :=
  tensorHomEquiv P Q T
example (P Q T : Complex A) (f : P ⊗ Q ⟶ T) :
    (tensorHomEquiv P Q T).symm (tensorHomEquiv P Q T f) = f :=
  (tensorHomEquiv P Q T).symm_apply_apply f
example (P Q : Complex A) :
    (P ◁ (ihom.coev P).app Q) ≫ (ihom.ev P).app (P ⊗ Q) = 𝟙 _ :=
  ihom.ev_coev _ _
example (P T : Complex A) :
    (ihom.coev P).app ((ihom P).obj T) ≫ (ihom P).map ((ihom.ev P).app T) = 𝟙 _ :=
  ihom.coev_ev _ _
end SerrePositivity.DifferentialGraded.Checks
#print axioms SerrePositivity.DifferentialGraded.homFunctor
#print axioms SerrePositivity.DifferentialGraded.homPrecompose
#print axioms SerrePositivity.DifferentialGraded.curryComponent_d
#print axioms SerrePositivity.DifferentialGraded.uncurryComponent_d
#print axioms SerrePositivity.DifferentialGraded.tensorRightHomEquiv
#print axioms SerrePositivity.DifferentialGraded.curryRight_naturality_source
#print axioms SerrePositivity.DifferentialGraded.curryRight_naturality_target
#print axioms SerrePositivity.DifferentialGraded.curryRight_naturality_domain
#print axioms SerrePositivity.DifferentialGraded.tensorRightHomAdjunction
#print axioms SerrePositivity.DifferentialGraded.complexMonoidalClosed
#print axioms SerrePositivity.DifferentialGraded.tensorHomEquiv_component
#print axioms SerrePositivity.DifferentialGraded.tensorHomEquiv_symm_component
#print axioms SerrePositivity.DifferentialGraded.tensorHomEquiv_naturality_domain
#print axioms SerrePositivity.DifferentialGraded.evaluation_component
