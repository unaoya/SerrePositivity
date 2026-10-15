module

public import SerrePositivity.PerfectComplex.CubicActionProjector

/-! # Lifting cubic eigenvectors to Fourier projector images -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]
namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} [Invertible (3 : R)]

/-- A chain eigenvector factors through the matching Fourier projector image. -/
def eigenvectorLift (τ : CochainCubicAction K) (a : R) (ha : a ^ 3 = 1)
    (f : L ⟶ K) (hf : f ≫ τ.map = a • f) : L ⟶ (τ.projector a ha).image :=
  equalizer.lift f (by
    rw [comp_id]
    exact (τ.eigenvector_comp_projectorMap a ha f hf).symm)

@[reassoc]
lemma eigenvectorLift_inclusion (τ : CochainCubicAction K) (a : R) (ha : a ^ 3 = 1)
    (f : L ⟶ K) (hf : f ≫ τ.map = a • f) :
    τ.eigenvectorLift a ha f hf ≫ (τ.projector a ha).inclusion = f :=
  equalizer.lift_ι _ _

end CochainCubicAction
end SerrePositivity
