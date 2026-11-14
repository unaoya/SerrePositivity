module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ArrowCalculus.DecompositionArrow
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ConeCFactor

/-! 同じ D 余単位の始域と円錐を、実 D 因子・C 因子の対象へ束ねる。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

def dgGluingDecompositionDFactor : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDecompositionDSource R C D M hC X,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDecompositionDSource_left_zero R C D M hC X⟩

def dgGluingDecompositionCFactor : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObject R C D M (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDecompositionDSource R C D M hC X) X
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDecompositionArrow R C D M hC X) hC hD,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObject_right_zero_of_isIso R C D M
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDecompositionDSource R C D M hC X) X
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDecompositionArrow R C D M hC X) hC hD
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDecompositionArrow_right_isIso R C D M hC X)⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
