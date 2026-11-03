module
public import SerrePositivity.DifferentialGraded.Derived.Projective

/-! # 実際の導来射集合と局所小性の受入検査 -/
@[expose] public section
universe u v
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example : LocallySmall.{u} (DerivedModuleCategory A D) := inferInstance

example (M N : DerivedModuleCategory A D) : Small.{u} (M ⟶ N) := inferInstance

#print axioms moduleResolutionDerivedHomEquiv
#print axioms moduleResolutionDerivedHomEquiv_map
#print axioms moduleResolutionDerivedHom_surjective
#print axioms moduleResolutionDerivedHom_eq_iff
#print axioms moduleDerivedHom_small
#print axioms moduleDerivedLocallySmall
