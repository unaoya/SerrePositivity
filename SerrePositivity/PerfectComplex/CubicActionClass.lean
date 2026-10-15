module

public import SerrePositivity.PerfectComplex.CubicActionDecomposition
public import SerrePositivity.KTheory.SupportedCoefficients
public import SerrePositivity.PerfectComplex.IdempotentImageClass

/-! # Weighted classes of cubic eigenspaces with extended coefficients -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace CochainCubicAction
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The integer K₀ class of one character eigenspace. -/
def eigenK0Class (τ : CochainCubicAction K) (t : R) (ht : t ^ 2 + t + 1 = 0)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) (j : Fin 3) :
    K0WithSupport Z :=
  (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).k0Class Z hp hs

/-- The ambient root determines the eigenspaces; the coefficient root weights their classes. -/
def weightedK0Class (E : Type v) [CommRing E]
    (τ : CochainCubicAction K) (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) :
    K0WithSupport.Coefficients E Z :=
  ∑ j : Fin 3, cubicCharacter ζ j ⊗ₜ[ℤ] τ.eigenK0Class t ht Z hp hs j

end CochainCubicAction
end SerrePositivity
