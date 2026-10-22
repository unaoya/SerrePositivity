module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DecompositionArrow
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeCFactor

/-! 同じ D 余単位の始域と円錐を、実 D 因子・C 因子の対象へ束ねる。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
  (X : DGGluingObject R C D M)

def dgGluingDecompositionDFactor : DGGluingDFactor R C D M :=
  ⟨dgGluingDecompositionDSource R C D M hC X,
    dgGluingDecompositionDSource_left_zero R C D M hC X⟩

def dgGluingDecompositionCFactor : DGGluingCFactor R C D M :=
  ⟨dgGluingConeObject R C D M (dgGluingDecompositionDSource R C D M hC X) X
      (dgGluingDecompositionArrow R C D M hC X) hC hD,
    dgGluingConeObject_right_zero_of_isIso R C D M
      (dgGluingDecompositionDSource R C D M hC X) X
      (dgGluingDecompositionArrow R C D M hC X) hC hD
      (dgGluingDecompositionArrow_right_isIso R C D M hC X)⟩

end SerrePositivity.InfinityCategories
