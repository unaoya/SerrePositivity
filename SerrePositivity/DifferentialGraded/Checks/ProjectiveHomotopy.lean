module
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-! # U10b6a：射影的始域からacyclic加群へのホモトピー -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {M N : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hN : moduleAcyclic A D N) (f : M ⟶ N) : Nonempty (ModuleHomotopy A D f 0) :=
  moduleHomotopicallyProjective_homotopy A D hM hN f 0

example {M N : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hN : moduleAcyclic A D N) (f g : M ⟶ N) :
    (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map g :=
  moduleHomotopicallyProjective_homotopy_map_eq A D hM hN f g

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms moduleHomotopicallyProjective_homotopy
#print axioms moduleHomotopicallyProjective_homotopy_map_eq
