module
public import SerrePositivity.DifferentialGraded.Derived.Projective

/-! # U10b7b：前合成のホモトピーと射影解像度比較への適用 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {M N : ModuleCategory A D} {f g : M ⟶ N} (h : ModuleHomotopy A D f g)
    (T : ModuleCategory A D) :
    Homotopy (eHomWhiskerRight (Complex A) f T) (eHomWhiskerRight (Complex A) g T) :=
  moduleHomPrecomposeHomotopy A D h T

example {M N : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hN : moduleHomotopicallyProjective A D N) (f : M ⟶ N) (hf : moduleQuasiIso A D f)
    (T : ModuleCategory A D) : HomotopyEquiv (N ⟶[Complex A] T) (M ⟶[Complex A] T) :=
  moduleProjectivePrecomposeHomotopyEquiv A D hM hN f hf T

example {M N : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hN : moduleHomotopicallyProjective A D N) (f : M ⟶ N) (hf : moduleQuasiIso A D f)
    (T : ModuleCategory A D) : QuasiIso (eHomWhiskerRight (Complex A) f T) :=
  moduleHomotopicallyProjective_precompose_quasiIso A D hM hN f hf T

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms modulePrecompositionMap
#print axioms modulePrecompositionMap_apply
#print axioms modulePrecompositionMap_d
#print axioms modulePrecompositionMap_closed
#print axioms moduleHomPrecomposeHomotopy
#print axioms moduleProjectivePrecomposeHomotopyEquiv
#print axioms moduleHomotopicallyProjective_precompose_quasiIso
