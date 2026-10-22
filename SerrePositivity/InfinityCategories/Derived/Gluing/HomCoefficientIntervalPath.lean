module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoefficientIntervalPathEndpoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTwoEndpointProduct

/-! 元の gluing Hom の同じ path を、νf から gμ への係数空間内の実区間族にする。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomCoefficientIntervalPath (X Y : DGGluingObject R C D M) :=
  complexPinchedMap.{u, max u v w} (dgGluingHomTwoEndpointPath R C D M X Y) ≫
    dgGluingCoefficientIntervalPathComparison.{u, max u v w} (M.value X.left Y.right)

lemma dgGluingHomCoefficientIntervalPath_start (X Y : DGGluingObject R C D M) :
    dgGluingHomCoefficientIntervalPath R C D M X Y ≫
        evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      complexPinchedMap.{u, max u v w}
        (dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y) := by
  rw [dgGluingHomCoefficientIntervalPath, Category.assoc,
    dgGluingCoefficientIntervalPathComparison_start, ← complexPinchedMap_comp,
    dgGluingHomTwoEndpointPath_start]

lemma dgGluingHomCoefficientIntervalPath_end (X Y : DGGluingObject R C D M) :
    dgGluingHomCoefficientIntervalPath R C D M X Y ≫
        evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      complexPinchedMap.{u, max u v w}
        (dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y) := by
  rw [dgGluingHomCoefficientIntervalPath, Category.assoc,
    dgGluingCoefficientIntervalPathComparison_end, ← complexPinchedMap_comp,
    dgGluingHomTwoEndpointPath_end]

lemma dgGluingHomCoefficientIntervalPath_endpoints (X Y : DGGluingObject R C D M) :
    dgGluingHomCoefficientIntervalPath R C D M X Y ≫
        F2.arrowEndpointPair (complexPinchedSpace.{u, max u v w} (M.value X.left Y.right)) =
      complexPinchedMap.{u, max u v w} (dgGluingHomTwoEndpointPath R C D M X Y) ≫
        dgGluingComplexPathSpaceEndpointPair.{u, max u v w} (M.value X.left Y.right) := by
  rw [dgGluingHomCoefficientIntervalPath, Category.assoc,
    dgGluingCoefficientIntervalPathComparison_endpoints]

end SerrePositivity.InfinityCategories
