module
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-! # U10b1：Hom end による性質と代表/零加群の証明 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (x : D) :
    moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) (representable A x)) :=
  representable_homotopicallyProjective A D x
example : moduleHomotopicallyProjective A D (moduleZero A D) :=
  moduleHomotopicallyProjective_of_isZero A D (moduleZero_isZero A D)
example : (moduleHomotopicallyProjective A D).IsClosedUnderIsomorphisms := inferInstance
example {M P : ModuleCategory A D} (e : M ≅ P) :
    moduleHomotopicallyProjective A D M ↔ moduleHomotopicallyProjective A D P :=
  (moduleHomotopicallyProjective A D).prop_iff_of_iso e
example {M : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (N : ModuleCategory A D) (hN : moduleAcyclic A D N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).Acyclic := hM N hN
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective
#print axioms SerrePositivity.DifferentialGraded.representable_homotopicallyProjective
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_of_iso
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopicallyProjectiveClosedUnderIso
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_of_isZero
