module

public import SerrePositivity.KTheory.Adams.TensorSquareEigenspaces
public import SerrePositivity.PerfectComplex.Eigen.Involution

/-! # Tensor-square eigenspaces preserve quasi-isomorphisms -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace Adams
variable {P Q : CochainComplex (ModuleCat.{u} R) ℤ}

abbrev tensorSquarePositiveMap (f : P ⟶ Q) : tensorSquarePositive P ⟶ tensorSquarePositive Q :=
  CochainInvolution.positiveImageMap (tensorSquareInvolution P) (tensorSquareInvolution Q)
    (tensorSquareMap f) (tensorSquareSwap_naturality f).symm

abbrev tensorSquareNegativeMap (f : P ⟶ Q) : tensorSquareNegative P ⟶ tensorSquareNegative Q :=
  CochainInvolution.negativeImageMap (tensorSquareInvolution P) (tensorSquareInvolution Q)
    (tensorSquareMap f) (tensorSquareSwap_naturality f).symm

lemma tensorSquarePositiveMap_quasiIso (f : P ⟶ Q) [QuasiIso f]
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    QuasiIso (tensorSquarePositiveMap f) := by
  have : QuasiIso (tensorSquareMap f) := cochainTensorMap_quasiIso hp hq hp hq f f
  exact CochainInvolution.positiveImageMap_quasiIso _ _ _ _

lemma tensorSquareNegativeMap_quasiIso (f : P ⟶ Q) [QuasiIso f]
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    QuasiIso (tensorSquareNegativeMap f) := by
  have : QuasiIso (tensorSquareMap f) := cochainTensorMap_quasiIso hp hq hp hq f f
  exact CochainInvolution.negativeImageMap_quasiIso _ _ _ _

lemma tensorSquarePositiveMap_homotopyEquivalence (f : P ⟶ Q) [QuasiIso f]
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (.up ℤ)
      (tensorSquarePositiveMap f) := by
  have := tensorSquarePositiveMap_quasiIso f hp hq
  exact (strictlyPerfectComplex_quasiIso_iff
    (tensorSquarePositive_perfect P hp) (tensorSquarePositive_perfect Q hq) _).mp inferInstance

lemma tensorSquareNegativeMap_homotopyEquivalence (f : P ⟶ Q) [QuasiIso f]
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (.up ℤ)
      (tensorSquareNegativeMap f) := by
  have := tensorSquareNegativeMap_quasiIso f hp hq
  exact (strictlyPerfectComplex_quasiIso_iff
    (tensorSquareNegative_perfect P hp) (tensorSquareNegative_perfect Q hq) _).mp inferInstance

end Adams
end SerrePositivity
