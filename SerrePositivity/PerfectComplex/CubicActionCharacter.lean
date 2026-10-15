module

public import SerrePositivity.PerfectComplex.CubicActionDecomposition

/-! # Scalar cubic actions associated to characters -/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory
variable {R : Type u} [CommRing R]
namespace CochainCubicAction

/-- The scalar action associated to one of the three characters. -/
def characterScalar (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (t : R) (ht : t ^ 3 = 1) (j : Fin 3) : CochainCubicAction K :=
  scalar K (cubicCharacter t j) (cubicCharacter_cube t ht j)

@[simp]
lemma characterScalar_map (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (t : R) (ht : t ^ 3 = 1) (j : Fin 3) :
    (characterScalar K t ht j).map = cubicCharacter t j • 𝟙 K := rfl

end CochainCubicAction
end SerrePositivity
