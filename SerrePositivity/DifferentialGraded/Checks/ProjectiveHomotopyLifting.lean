module
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomotopyHom

/-! # U10b6e：ホモトピーまでの持ち上げ・一意性とK(D)のHom -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {T M N : ModuleCategory A D} (hT : moduleHomotopicallyProjective A D T)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) (g : T ⟶ N) :
    ∃ s : T ⟶ M, Nonempty (ModuleHomotopy A D (s ≫ f) g) :=
  moduleHomotopicallyProjective_homotopy_lift A D hT f hf g

example {T M N : ModuleCategory A D} (hT : moduleHomotopicallyProjective A D T)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    Function.Bijective (fun s : (moduleToHomotopy A D).obj T ⟶ (moduleToHomotopy A D).obj M =>
      s ≫ (moduleToHomotopy A D).map f) :=
  moduleHomotopicallyProjective_homotopy_postcompose_bijective A D hT f hf

example {M N : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hN : moduleHomotopicallyProjective A D N) (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    IsIso ((moduleToHomotopy A D).map f) :=
  moduleHomotopicallyProjective_quasiIso_isIso_homotopy A D hM hN f hf

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms complexCone_d_fst
#print axioms complexCone_d_snd
#print axioms complexAcyclic_boundary_succ
#print axioms complexQuasiIso_cycle_lift
#print axioms complexQuasiIso_boundary_reflect
#print axioms moduleMorphismOfCycle
#print axioms moduleMorphismOfCycle_cycle
#print axioms moduleHomCycle_postcompose
#print axioms moduleHomotopicallyProjective_homotopy_lift
#print axioms moduleHomotopicallyProjective_homotopy_reflect
#print axioms moduleHomotopicallyProjective_postcompose_map_eq_iff
#print axioms moduleHomotopicallyProjective_homotopy_postcompose_bijective
#print axioms moduleHomotopicallyProjective_quasiIso_isIso_homotopy
