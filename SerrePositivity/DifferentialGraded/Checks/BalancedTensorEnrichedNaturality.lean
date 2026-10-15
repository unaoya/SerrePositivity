module
public import SerrePositivity.DifferentialGraded.Tensor.YonedaEnriched

/-! # tensorの左右交換とYonedaの全Hom自然性の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory CochainComplex HomComplex SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (M M' : RightModule A D) (N N' : LeftModule A D)
    (τ : (moduleHom A D M M').X 1) (σ : (leftModuleHom A D N N').X 1) :
    (((BalancedTensor.rightHomMap A D M M' N).f 1 τ).comp
      ((BalancedTensor.leftHomMap A D M' N N').f 1 σ) (show 1 + 1 = (2 : ℤ) from rfl)) =
    (1 * 1 : ℤ).negOnePow • (((BalancedTensor.leftHomMap A D M N N').f 1 σ).comp
      ((BalancedTensor.rightHomMap A D M M' N').f 1 τ) (show 1 + 1 = (2 : ℤ) from rfl)) :=
  BalancedTensor.homMaps_interchange A D τ σ rfl

#print axioms BalancedTensor.homMaps_interchange
#print axioms BalancedTensor.yonedaEvaluation_enriched_naturality
#print axioms BalancedTensor.leftYonedaEvaluation_enriched_naturality
