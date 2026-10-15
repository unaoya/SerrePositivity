module
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveResolutionLift

/-! # U10b7e：解像度への射の持ち上げと関手法則 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {M N : ModuleCategory A D} (P : ModuleProjectiveResolution A D M)
    (Q : ModuleProjectiveResolution A D N) (f : M ⟶ N) :
    (moduleToHomotopy A D).map (P.lift Q f) ≫ (moduleToHomotopy A D).map Q.π =
      (moduleToHomotopy A D).map P.π ≫ (moduleToHomotopy A D).map f := P.lift_fac Q f

example {M N L : ModuleCategory A D} (P : ModuleProjectiveResolution A D M)
    (Q : ModuleProjectiveResolution A D N) (R : ModuleProjectiveResolution A D L)
    (f : M ⟶ N) (g : N ⟶ L) :
    (moduleToHomotopy A D).map (P.lift Q f) ≫ (moduleToHomotopy A D).map (Q.lift R g) =
      (moduleToHomotopy A D).map (P.lift R (f ≫ g)) := P.lift_comp Q R f g

example {M N : ModuleCategory A D} (P P' : ModuleProjectiveResolution A D M)
    (Q Q' : ModuleProjectiveResolution A D N) (f : M ⟶ N) :
    (moduleToHomotopy A D).map (P.lift Q f) ≫ (moduleToHomotopy A D).map (Q.comparison Q') =
      (moduleToHomotopy A D).map (P.comparison P') ≫
        (moduleToHomotopy A D).map (P'.lift Q' f) := P.lift_comparison_naturality P' Q Q' f

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms ModuleProjectiveResolution.lift
#print axioms ModuleProjectiveResolution.lift_fac
#print axioms ModuleProjectiveResolution.lift_unique
#print axioms ModuleProjectiveResolution.lift_id
#print axioms ModuleProjectiveResolution.lift_comp
#print axioms ModuleProjectiveResolution.lift_quasiIso
#print axioms ModuleProjectiveResolution.lift_id_comparison
#print axioms ModuleProjectiveResolution.lift_comparison_naturality
