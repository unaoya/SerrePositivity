module

public import SerrePositivity.PerfectComplex.CubicActionTensorRows
public import SerrePositivity.PerfectComplex.IdempotentImagePerfect
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent

/-! # Tensor eigenspaces as sums of three matching character tensor products -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The three row projector images form one eigenspace of the tensor action. -/
def tensorCharacterRowDecompositionIso (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (l : Fin 3) :
    (⨁ fun i : Fin 3 => (τ.tensorCharacterRowProjector σ t ht l i).image) ≅
      ((τ.tensor σ).characterProjector t (cube_eq_one_of_cubic_relation t ht) l).image :=
  CochainIdempotent.imageFiniteSumIso _ _
    (tensorCharacterRowProjector_orthogonal τ σ t ht l)
    (sum_tensorCharacterRowProjector_map τ σ t ht l)

/-- Sum the j and l-j eigenspace tensor products to obtain the l eigenspace. -/
def tensorCharacterEigenIso (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (l : Fin 3) :
    (⨁ fun i : Fin 3 => cochainTensor
      (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) i).image
      (σ.characterProjector t (cube_eq_one_of_cubic_relation t ht) (l - i)).image) ≅
        ((τ.tensor σ).characterProjector t (cube_eq_one_of_cubic_relation t ht) l).image :=
  biproduct.mapIso (fun i : Fin 3 => CochainIdempotent.imageTensorIso
    (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) i)
    (σ.characterProjector t (cube_eq_one_of_cubic_relation t ht) (l - i))) ≪≫
      tensorCharacterRowDecompositionIso τ σ t ht l

end CochainCubicAction
end SerrePositivity
