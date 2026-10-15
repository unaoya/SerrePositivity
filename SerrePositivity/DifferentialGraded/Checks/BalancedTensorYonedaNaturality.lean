module
public import SerrePositivity.DifferentialGraded.Tensor.YonedaNaturality

/-! # Yoneda評価の通常射・任意次数Homに関する自然性の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Opposite SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example {N N' : LeftModule A D} (τ : (leftModuleHom A D N N').X (-1))
    (x y : D) (f : GradedHom A x y 1) (m : (N.obj x).X 0) :
    (((leftModuleHomπ A D N N' y).f (-1) τ).v 1 0 (by omega))
      (leftAction A N f m (by omega)) =
    ((-1) * 1 : ℤ).negOnePow • leftAction A N' f
      ((((leftModuleHomπ A D N N' x).f (-1) τ).v 0 (-1) (by omega)) m) (by omega) :=
  leftModuleHomElement_action A D τ x y f m (by omega) (by omega) (by omega)

#print axioms leftModuleHomπ
#print axioms leftModuleHomElement_naturality
#print axioms leftModuleHomElement_action
#print axioms BalancedTensor.yonedaEvaluation_naturality
#print axioms BalancedTensor.leftYonedaEvaluation_naturality
#print axioms BalancedTensor.yonedaEvaluation_homElement
#print axioms BalancedTensor.leftYonedaEvaluation_homElement
