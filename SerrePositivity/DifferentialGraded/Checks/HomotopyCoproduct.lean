module
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom

/-! # K(D)の余積の受入検査 -/
@[expose] public section
universe u v w
open CategoryTheory Limits SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (J : Type w) [Small.{u} J]

example : HasColimitsOfShape (Discrete J) (ModuleHomotopyCategory A D) := inferInstance

example (M : J → ModuleCategory A D) :
    PreservesColimit (Discrete.functor M) (moduleToHomotopy A D) := inferInstance

#print axioms moduleHomCycle_precompose
#print axioms moduleCoproduct_homotopy_of_components
#print axioms moduleHomotopyCoproduct_hom_ext
#print axioms moduleHomotopyCofan
#print axioms moduleHomotopyCofanDesc
#print axioms moduleHomotopyCofanDesc_fac
#print axioms moduleHomotopyCofanIsColimit
#print axioms moduleHomotopyHasCoproductsOfShape
#print axioms moduleToHomotopyPreservesCoproduct
