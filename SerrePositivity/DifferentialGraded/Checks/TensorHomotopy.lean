module
public import SerrePositivity.DifferentialGraded.Tensor.ProjectiveKFlat
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # dgホモトピー保存と解像度比較のtensor像 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BalancedTensor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (L : LeftModule A D) {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) :
    Nonempty (Homotopy (rightTensorMap A D L f) (rightTensorMap A D L g)) :=
  rightTensorMap_homotopy A D L h

example (L : LeftModule A D) {M N : ModuleCategory A D}
    (hM : moduleSemifree A D M) (hN : moduleSemifree A D N)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    QuasiIso ((rightTensorFunctor A D L).map f) :=
  rightTensor_semifree_quasiIso A D L hM hN f hf

example (L : LeftModule A D) {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    (rightTensorProjectiveHomotopyEquiv A D L hM hN f hf).hom =
      (rightTensorFunctor A D L).map f := rfl

example (L : LeftModule (ZMod 2) PUnit.{1}) {M N : ModuleCategory (ZMod 2) PUnit.{1}}
    {f g : M ⟶ N} (h : ModuleHomotopy (ZMod 2) PUnit.{1} f g) :
    Nonempty (Homotopy (rightTensorMap (ZMod 2) PUnit.{1} L f)
      (rightTensorMap (ZMod 2) PUnit.{1} L g)) :=
  rightTensorMap_homotopy (ZMod 2) PUnit.{1} L h

#print axioms rightHomMap_closedElement
#print axioms rightTensorDG_map
#print axioms rightTensorMap_homotopy
#print axioms rightTensorHomotopyFunctor
#print axioms rightTensorHomotopyFunctor_fac
#print axioms rightTensorProjectiveHomotopyEquiv
#print axioms rightTensor_projective_quasiIso
#print axioms rightTensor_semifree_quasiIso
#print axioms moduleHomotopicallyProjective_relativeKFlat
