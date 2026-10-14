module

public import SerrePositivity.PerfectComplex.CubicActionProjector
public import SerrePositivity.PerfectComplex.TensorHomotopy

/-! # Tensor products of cubic cochain actions -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]
namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Simultaneously act on the two tensor factors. -/
def tensor (τ : CochainCubicAction K) (σ : CochainCubicAction L) :
    CochainCubicAction (cochainTensor K L) where
  map := cochainTensorMap τ.map σ.map
  cube := by
    rw [cochainTensorMap_comp, cochainTensorMap_comp, τ.cube, σ.cube, cochainTensorMap_id]

end CochainCubicAction
end SerrePositivity
