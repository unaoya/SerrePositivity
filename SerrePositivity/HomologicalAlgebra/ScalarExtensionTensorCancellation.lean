module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorBaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Tensor cancellation for scalar extension and an arbitrary module over the new ring -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory MonoidalCategory TensorProduct
open scoped TensorProduct ChangeOfRings
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- The ordinary tensor projection formula for an arbitrary module over S. -/
def scalarExtensionTensorCancelIso (N : ModuleCat.{u} S) :
    ModuleCat.extendScalars φ ⋙ (tensoringLeft (ModuleCat S)).obj N ⋙
        ModuleCat.restrictScalars φ ≅
      (tensoringLeft (ModuleCat R)).obj ((ModuleCat.restrictScalars φ).obj N) := by
  letI := φ.toAlgebra
  letI : Module R N := Module.compHom N φ
  letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact ((AlgebraTensorModule.cancelBaseChange R S S N M).restrictScalars R).toModuleIso
  · intro M M' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (LinearMap.congr_fun
      (AlgebraTensorModule.lTensor_comp_cancelBaseChange R S S (M := N) f.hom) x).symm

end SerrePositivity
