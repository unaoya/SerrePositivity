module

public import SerrePositivity.KTheory.Adams.TensorCubeEigenspaces
public import SerrePositivity.PerfectComplex.IdempotentImageQuasiIso

/-! # Tensor-cube character maps preserve quasi-isomorphisms -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
namespace Adams
variable {R : Type u} [CommRing R]
variable {P Q : CochainComplex (ModuleCat.{u} R) ℤ}

lemma tensorCubeMap_quasiIso (f : P ⟶ Q) [QuasiIso f]
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    QuasiIso (tensorCubeMap f) := by
  have : QuasiIso (tensorSquareMap f) := cochainTensorMap_quasiIso hp hq hp hq f f
  exact cochainTensorMap_quasiIso (tensorSquare_perfect P hp) (tensorSquare_perfect Q hq)
    hp hq (tensorSquareMap f) f

variable [Invertible (3 : R)] (t : R) (ht : t ^ 2 + t + 1 = 0)

lemma tensorCubeEigenspaceMap_quasiIso (f : P ⟶ Q) [QuasiIso f]
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) (j : Fin 3) :
    QuasiIso (tensorCubeEigenspaceMap t ht f j) := by
  have := tensorCubeMap_quasiIso f hp hq
  exact CochainIdempotent.imageMap_quasiIso _ _ _ _

lemma tensorCubeEigenspaceMap_homotopyEquivalence (f : P ⟶ Q) [QuasiIso f]
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) (j : Fin 3) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (.up ℤ)
      (tensorCubeEigenspaceMap t ht f j) := by
  have := tensorCubeEigenspaceMap_quasiIso t ht f hp hq j
  exact (strictlyPerfectComplex_quasiIso_iff
    (tensorCubeEigenspace_perfect t ht P hp j)
    (tensorCubeEigenspace_perfect t ht Q hq j) _).mp inferInstance

end Adams
end SerrePositivity
